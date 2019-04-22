module App

// ------------------------------------------------------------------------------------------------
// Types
// ------------------------------------------------------------------------------------------------

type Reference = 
  | Named of string
  | Indexed of int

type ObjectValue = 
  abstract Lookup : string -> Value
  abstract Preview : (unit -> unit) -> Tbd.Html.DomNode
  abstract Hash : int

and Value =
  | OperationValue of (Value list -> Value)
  | PrimitiveValue of obj
  | ObjectValue of ObjectValue

type Expr = 
  | External of string
  | Value of Value * Type
  | Member of Reference * string
  | Invocation of Reference * Reference list

and ObjectType = 
  abstract Members : (string * Type) list

and Type = 
  | PrimitiveType of string
  | OperationType of (string * Type) list * Type
  | ObjectType of ObjectType

type Completion = 
  | Dot of Reference * string
  | Apply of Reference * string * Reference

type Interaction =
  | Completions of Reference 
  | Complete of Completion
  | Name of Reference * string
  | Evaluate of Reference 
  | Abstract of Reference list * Reference
  | DefineValue of Value * Type
  | ReplaceValue of Reference * Value * Type

type Code = 
  { Source : list<Reference * Expr>
    Values : Map<Reference, int * Value>
    Arguments : Map<string, Reference> option
    Counter : int
    Completions : (Reference * ((string * Completion) list)) option }

type Program = list<Interaction> 

type Context = 
  { External : Map<string, Value * Type> }

let find key l = List.find (fun (k, _) -> k = key) l |> snd

let getMemberTypes ty = 
  let f n = fun a r -> n, OperationType(a, r)
  let (@) f (a, b) = f [a, PrimitiveType b]
  let (=>) f r = f (PrimitiveType r)
  match ty with
  | ObjectType o -> o.Members
  | PrimitiveType "bool" -> 
      [ f "and" @ ("other", "bool") => "bool"
        f "or" @ ("other", "bool") => "bool" ]
  | PrimitiveType "number" -> 
      [ f "equals" @ ("other", "number") => "bool"
        f "not equals" @ ("other", "number") => "bool" ]
  | PrimitiveType "string" ->
      [ f "equals" @ ("other", "string") => "bool"
        f "not equals" @ ("other", "string") => "bool" ]
  | t -> failwithf "getMemberTypes: Cannot get members on %s" (string t)

let getMemberValue m v = 
  let f v g = OperationValue(function 
    | [PrimitiveValue other] -> PrimitiveValue(g (unbox v) (unbox other)) 
    | _ -> failwith "getMemberValue: Bad arguments")
  match v with
  | ObjectValue v -> v.Lookup m
  | PrimitiveValue v when m = "equals" -> f v (fun a b -> a = b)
  | PrimitiveValue v when m = "not equals" -> f v (fun a b -> a <> b)
  | PrimitiveValue v when m = "and" -> f v (fun a b -> a && b)
  | PrimitiveValue v when m = "or" -> f v (fun a b -> a || b)
  | _ -> failwithf "Cannot access member '%s' of a primitive value" m

let rec typesMatch t1 t2 =
  match t1, t2 with 
  | ObjectType(o1), ObjectType(o2) ->
      List.forall2 (fun a1 a2 -> typesMatch (snd a1) (snd a2)) o1.Members o2.Members // TODO: Structural typing for objects
  | PrimitiveType t1, PrimitiveType t2 -> t1 = t2
  | OperationType(args1, res1), OperationType(args2, res2) ->
      typesMatch res1 res2 &&
      List.forall2 (fun a1 a2 -> typesMatch (snd a1) (snd a2)) args1 args2 
  | _ -> false

let rec typeCheck ctx code expr = 
  match expr with
  | Value(value, typ) -> typ

  | Invocation(op, args) ->
      match typeCheck ctx code (find op code.Source) with 
      | OperationType(expectedArgs, res) ->
          let argTys = [ for a in args -> typeCheck ctx code (find a code.Source) ]
          for (n, expected), actual in List.zip expectedArgs argTys do 
            if not (typesMatch expected actual) then
              failwithf "Type mismatch (or cannot compare): '%s' and '%s'" (string expected) (string actual)
          res

      | ty -> failwithf "Cannot invoke non-operation typed thing of type: %s" (string ty)
  
  | External(s) -> snd ctx.External.[s]
  | Member(ref, name) ->
      let mems = typeCheck ctx code (find ref code.Source) |> getMemberTypes
      match Seq.tryFind (fun (n, _) -> n = name) mems with
      | None -> failwithf "Member %s not found" name
      | Some(_, t) -> t

let rec getInputs code ref = 
  match find ref code.Source with
  | Value _ -> Set.empty
  | Invocation(ref, args) -> 
      List.foldBack Set.add (ref::args)
        (Set.unionMany (List.map (getInputs code) (ref::args)))      
  | External e -> Set.empty
  | Member(r, m) -> 
      Set.add r (getInputs code r)

let rec hashCode code ref = 
  match find ref code.Source with
  | Value(PrimitiveValue v, PrimitiveType t) -> hash (v, t)
  | Value(ObjectValue o, ObjectType _) -> o.Hash
  | Value(OperationValue _, OperationType _) -> 42 // TODO: Find some clever way of hashing functions...
  | Value(v, t) -> failwithf "Cannot hash non-primitive values: %A" (v, t)
  | Invocation(ref, args) -> hash [ for r in ref::args -> hashCode code r ]
  | External e -> hash e
  | Member(r, m) -> hash (hashCode code r, m)

let rec evaluate ctx code (values:Map<Reference, int * Value>) ref = 
  match Map.tryFind ref values with
  | Some(h, v) when hashCode code ref = h -> v, values
  | _ ->
      match find ref code.Source with
      | Value(v, _) ->
          v, Map.add ref (hashCode code ref, v) values

      | Invocation(refInst, args) ->
          match evaluate ctx code values refInst with 
          | OperationValue(f), values ->
              let args, values = args |> List.fold (fun (args, values) arg ->
                let arg, values = evaluate ctx code values arg
                arg::args, values) ([], values)
              let v = f (List.rev args)
              v, Map.add ref (hashCode code ref, v) values
          | v, _ -> 
              failwithf "evaluate: Cannot invoke non-operation-valued thing at %s: %s" (string ref) (string v)

      | External e -> 
          let v = fst (ctx.External.[e])
          v, Map.add ref (hashCode code ref, v) values

      | Member(inst, m) ->
          let v, values = evaluate ctx code values inst
          let v = getMemberValue m v 
          v, Map.add ref (hashCode code ref, v) values

let rec apply ctx code interaction =
  match interaction with
  | Abstract(argRefs, res) ->
      let v = OperationValue (fun argVals ->
        let replaces = 
          List.zip argRefs argVals 
          |> List.map (fun (r, v) -> ReplaceValue(r, v, typeCheck ctx code (find r code.Source)))
        let virtualCode = 
          List.append replaces [ Evaluate(res) ]
          |> List.fold (apply ctx) code
        virtualCode.Values.[res] |> snd )
      let argTys = 
        [ for i, r in Seq.indexed argRefs -> 
            sprintf "arg%d" i, typeCheck ctx code (find r code.Source) ]
      let t = OperationType(argTys, typeCheck ctx code (find res code.Source))
      let nexpr = Value(v, t)
      let nref = Indexed(code.Counter)
      { code with Source = code.Source @ [ (nref, nexpr) ]; Counter = code.Counter + 1 }

  | ReplaceValue(ref, v, t) ->
      let nexpr = Value(v, t)
      let nsource = code.Source |> List.map (fun (r, e) -> if r = ref then r, nexpr else r, e)
      { code with Source = nsource }

  | DefineValue(v, t) ->
      let nexpr = Value(v, t)
      let nref = Indexed(code.Counter)
      { code with Source = code.Source @ [ (nref, nexpr) ]; Counter = code.Counter + 1 }

  | Completions(ref) ->
      let ty = typeCheck ctx code (find ref code.Source)
      match ty with 
      | OperationType(args, res) ->
          let appliedArgs = defaultArg code.Arguments Map.empty
          let args = args |> List.filter (fst >> appliedArgs.ContainsKey >> not)
          let srcTypes = [ for ref, c in code.Source -> ref, typeCheck ctx code c ]
          let compl = 
            [ for arg, argTy in args do
              for src, srcTy in srcTypes do
              //printf "Considering: %A = %A\n - Arg ty: %A\n - Src ty: %A\n - Matches: %A" arg src argTy srcTy (typesMatch argTy srcTy)
              if typesMatch argTy srcTy then
                yield arg + " = " + string src, Apply(ref, arg, src) ]
          { code with Completions = Some(ref, compl) }
      | ty ->
          let compl = [ for m, _ in getMemberTypes ty -> m, Dot(ref, m) ]
          { code with Completions = Some(ref, compl) }
  
  | Complete completion ->
      match completion with
      | Apply(opRef, arg, argRef) ->
          let actualArgs = defaultArg code.Arguments Map.empty |> Map.add arg argRef
          let actualSet = set [ for kvp in actualArgs -> kvp.Key ]
          match typeCheck ctx code (find opRef code.Source) with 
          | OperationType(expectedArgs, res) when actualSet = set (List.map fst expectedArgs) ->
              let nexpr = Invocation(opRef, [ for n, _ in expectedArgs -> actualArgs.[n]])
              let nref = Indexed(code.Counter)
              { code with Source = code.Source @ [ (nref, nexpr) ]; Arguments = None; Counter = code.Counter + 1; Completions = None }
          | _ -> 
              { code with Arguments = Some actualArgs }

      | Dot(ref, m) -> 
          let nexpr = Member(ref, m)
          let nref = Indexed(code.Counter)
          { code with Source = code.Source @ [ (nref, nexpr) ]; Counter = code.Counter + 1; Completions = None }

  | Name(ref, name) ->
      { code with Source = code.Source @ [ (Named name, find ref code.Source) ] }

  | Evaluate(ref) ->
      { code with Values = snd (evaluate ctx code code.Values ref) }


// ------------------------------------------------------------------------------------------------
// User interface
// ------------------------------------------------------------------------------------------------

open Elmish
open Tbd.Html
open Fable.Core
open Fable.Import
open Fable.PowerPack
open Fable.PowerPack.Keyboard

let renderTable data = 
  h?table ["class"=>"data"] [
    for row in data -> h?tr [] [
      for col in row -> h?td [] [ text (string col) ]
    ]
  ]


type Model = 
  { Program : Program 
    Context : Context
    Code : Code

    CurrentFunction : Reference option
    CurrentReplace : (Reference * string) option
    CurrentValue : string option  
    CurrentName : (Reference * string) option }
    
type Event = 
  | Interact of Interaction
  | Refresh

  | UpdateCurrentFunction of Reference option

  | FinishReplace
  | UpdateReplace of (Reference * string) option

  | FinishAddValue
  | UpdateAddValue of string option

  | FinishNaming 
  | UpdateName of (Reference * string) option

let interact op model =
  { model with Program = model.Program @ [op]; Code = apply model.Context model.Code op }

let parse s = 
  match System.Int32.TryParse(s) with 
  | true, r -> PrimitiveType "number", PrimitiveValue r 
  | _ -> PrimitiveType "string", PrimitiveValue s

let update model = function
  | Refresh -> model

  | UpdateCurrentFunction f ->
      { model with CurrentFunction = f }

  | UpdateReplace r ->
      { model with CurrentReplace = r }
  | FinishReplace ->
      let ref, s = model.CurrentReplace.Value
      let t, v = parse s
      { model with CurrentReplace = None } |> interact (ReplaceValue(ref, v, t))

  | UpdateAddValue s -> 
      { model with CurrentValue = s }
  | FinishAddValue ->
      let t, v = parse (defaultArg model.CurrentValue "")
      { model with CurrentValue = None } |> interact (DefineValue(v, t))
  
  | UpdateName(rn) ->
      { model with CurrentName = rn }
  | FinishNaming ->
      match model.CurrentName with 
      | Some(ref, n) -> { model with CurrentName = None } |> interact (Name(ref, n))
      | _ -> failwith "Cannot finish naming when current name is none"

  | Interact i -> 
      model |> interact i

let cols els = 
  h?table [] [
    h?tr [] [ for e in els -> h?td [ "class" => "cell" ] [ e ] ]
  ]
let rows els = 
  h?table [] [ 
    for e in els -> h?tr [] [ h?td [ "class" => "cell" ] [ e ] ] 
  ]

let renderPreview trigger (v:Value) = 
  h?div ["class" => "preview" ] [ 
    match v with 
    | OperationValue v -> yield text ("(Operation)")
    | ObjectValue v -> yield h?div [] [ text "Object:"; v.Preview(fun () -> trigger Refresh) ]
    | PrimitiveValue v -> yield text ("Primitive: " + string v) ]

let rec formatReference code ref = 
  match ref with 
  | Indexed n -> formatExpression code (find ref code.Source)
  | Named n -> n

and formatExpression code = function
  | External s -> sprintf "extern('%s')" s
  | Value(OperationValue v, _) -> "function"
  | Value(PrimitiveValue v, PrimitiveType "string") -> sprintf "value('%s')" (string v)
  | Value(PrimitiveValue v, _) -> sprintf "value(%s)" (string v)
  | Value(v, _) -> sprintf "value(%s)" (string v)
  | Member(ref, s) -> sprintf "%s.%s" (formatReference code ref) s
  | Invocation(ref, args) -> sprintf "%s(%s)" (formatReference code ref) (String.concat ", " (List.map (formatReference code) args))

let renderCode trigger state = 
  let named = state.Program |> List.choose (function Name(ref, _) -> Some ref | _ -> None) |> set
  let nonHidden = state.Code.Source |> List.filter (fun (k, _) -> not (Set.contains k named))
  let getValue k = state.Code.Values.TryFind(k) |> Option.bind (fun (h, v) -> if hashCode state.Code k = h then Some v else None)
  cols [ 
    for k, v in nonHidden -> h?div [] [
      yield h?strong [] [ text (string k) ]
      yield h?br [] []
      yield text (formatExpression state.Code v)
      yield h?br [] []

      match v, state.CurrentReplace with
      | Value(_, PrimitiveType t), Some(ref, v) when ref = k ->
          yield h?input [ 
            "input" =!> fun e _ -> trigger(UpdateReplace(Some(ref, unbox<Browser.HTMLInputElement>(e).value))) 
            "keydown" =!> fun _ k -> 
              match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
              | 13 -> trigger(FinishReplace)
              | 27 -> trigger(UpdateReplace None)
              | _ -> ()
            ] []
          yield h?br [] []
      | Value(v, PrimitiveType t), _ ->
          yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(UpdateReplace(Some(k, ""))) ] [ text "replace" ]
          yield h?br [] []
      | _ -> ()

      match state.CurrentName with
      | Some(ref, n) when ref = k ->
          yield h?input [ 
            "value" => n
            "input" =!> fun e _ -> trigger(UpdateName(Some(ref, unbox<Browser.HTMLInputElement>(e).value))) 
            "keydown" =!> fun _ k -> 
              match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
              | 13 -> trigger(FinishNaming)
              | 27 -> trigger(UpdateName None)
              | _ -> ()
            ] []
      | _ ->
          yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(UpdateName(Some(k, ""))) ] [ text "name" ]
          yield h?br [] []

      match state.CurrentFunction with
      | Some ref when ref = k -> 
          yield rows [
            for inp in getInputs state.Code ref ->
              h?button ["click" =!> fun _ _ -> trigger(Interact(Abstract([inp], k)))] [ text ("taking " + string inp) ]
          ]
      | _ -> 
        yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(UpdateCurrentFunction(Some(k))) ] [ text "function" ]
        yield h?br [] []

      match state.Code.Completions with
      | Some(ref, compl) when k = ref ->
          yield rows [
            for n, c in compl -> h?button ["click" =!> fun _ _ -> trigger(Interact(Complete c)) ] [ text n]
          ]
      | _ ->
          yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(Interact(Completions k)) ] [ text "completions" ]
          yield h?br [] []

      match getValue k with
      | Some(v) ->
          yield renderPreview trigger v
      | None -> 
          yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(Interact(Evaluate k)) ] [ text "evaluate" ]
          yield h?br [] []      
      ]
    yield h?div [] [
      if state.CurrentValue = None then
        yield h?a [ "href"=>"#"; "click" =!> fun _ _ -> trigger(UpdateAddValue (Some "")) ] [ text "add value" ]
      else
        yield text "Add value"
        yield h?br [] [] 
        yield h?input [ 
          "input" =!> fun e _ -> trigger(UpdateAddValue(Some(unbox<Browser.HTMLInputElement>(e).value))) 
          "keydown" =!> fun _ k -> 
            match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
            | 13 -> trigger(FinishAddValue)
            | 27 -> trigger(UpdateAddValue None)
            | _ -> () ] []
    ]
  ]

let view trigger state =
  Browser.console.log("PROGRAM")
  for p in state.Program do Browser.console.log(" * ", string p)
  renderCode trigger state 


// ------------------------------------------------------------------------------------------------
// Demo types
// ------------------------------------------------------------------------------------------------

let downlaod url = 
  Async.FromContinuations (fun (cont, _, _) ->
    let data = Fetch.fetch url []
    ignore(data.``then``(fun v -> 
      ignore (v.text().``then``(fun v -> 
        let data = v.Split('\n') |> Array.filter (fun row -> row.Trim() <> "") |> Array.map (fun row -> row.Split(','))
        cont data )))))
(*
let load file = 
  let data = Fetch.fetch file []
  let mutable result = None
  let mutable handlers = ResizeArray<_>()
  let res = data.``then``(fun v -> v.text().``then``(fun v -> 
    let data = v.Split('\n') |> Array.map (fun row -> row.Split(','))
    result <- Some data
    for h in handlers do h () ))
  { new ObjectValue with 
      member x.Preview f = 
        handlers.Add f 
        match result with 
        | None -> text "Loading..."
        | Some data -> renderTable (Seq.truncate 10 data)
      member x.Lookup _ = failwith "Member not found" } |> ObjectValue

let data = 
  { new ObjectValue with
    member x.Preview _ = text "(Dataset)"
    member x.Lookup m =
      match m with
      | "air" -> load "data/avia.csv"
      | "train" -> load "data/rail.csv"
      | _ -> failwith "Member not found" } |> ObjectValue,
  { new ObjectType with
      member x.Members = ["air", PrimitiveType "unit"; "train", PrimitiveType "unit"] } |> ObjectType
*)

let row headers values =
  //printfn "Creating row\n  - headers: %A\n  - values: %A" headers values 
  let data = List.zip headers values
  let parse v = match System.Int32.TryParse(v) with true, r -> PrimitiveType "number", PrimitiveValue r | _ -> PrimitiveType "string", PrimitiveValue v
  { new ObjectValue with
    member x.Hash = hash values
    member x.Preview _ = renderTable [ for k, v in data -> [k;v] ]
    member x.Lookup m = data |> Seq.pick (fun (k, v) -> if k = m then Some(snd (parse v)) else None) } |> ObjectValue,
  { new ObjectType with
      member x.Members = [ for k, v in data -> k, fst (parse v) ] } |> ObjectType

let dataArray file = async {
  let! data = downlaod file
  let headers = data.[0] |> List.ofArray
  let rows = data.[1..] |> Array.map (fun a -> let v, t = row headers (List.ofArray a) in a, v, t)
  let rec v (rows:(string[] * Value * Type)[]) = 
    { new ObjectValue with
      member x.Hash = hash [for _, (ObjectValue r), _ in rows -> r.Hash ]
      member x.Preview _ = 
        h?div [] [ 
          h?p [] [ text (sprintf "Table with %d rows" rows.Length)]
          renderTable (Seq.truncate 10 [for a, _, _ in rows -> a]) 
        ]
      member x.Lookup m = 
        if m = "at" then OperationValue(function  
          | [PrimitiveValue n] -> 
              let _, v, _ = (Array.item (unbox n) rows) in v 
          | _ -> failwith "dataArray.at: Invalid index")

        elif m = "filter" then OperationValue(function 
          | [OperationValue f] -> 
              rows |> Array.filter (fun (_, r, _) -> 
                let res = f [r]
                //printfn "Filtering (%A): %A" (let (PrimitiveValue b) = res in unbox b = true) r
                match res with PrimitiveValue(b) -> unbox b = true | _ -> false) |> v
          | _ -> failwith "dataArray.filter: Invalid predicate")
        else failwith "dataArray: Member not found"
        //else fst (Array.item (int m) rows) 
        } |> ObjectValue
  let rec t = 
    { new ObjectType with
        member x.Members = 
          let _, _, mt = Array.item 0 rows
          [ yield "at", OperationType(["index", PrimitiveType "number"], mt)
            yield "filter", OperationType(["predicate", OperationType(["row", mt], PrimitiveType "bool")], t)
            //for i, (_, t) in Seq.indexed rows -> string i, t 
            ] } |> ObjectType
  return v rows, t }

let initial = 
  { Completions = None 
    Arguments = None
    Source = [ Named "avia", External "avia"; Named "rail", External "rail" ]
    Values = Map.empty
    Counter = 0 }

Async.StartImmediate <| async {
  let! avia = dataArray "data/avia.csv"
  let! rail = dataArray "data/rail.csv"
  let ctx = { External = Map.ofList ["avia", avia; "rail", rail] }
  let prog = 
    [ DefineValue (PrimitiveValue 2500,PrimitiveType "number") 
      Completions (Named "avia")
      Complete (Dot (Named "avia","at"))
      Completions (Indexed 1)
      Complete (Apply (Indexed 1,"index",Indexed 0))
      Evaluate (Indexed 2)
      Completions (Indexed 2)
      Complete (Dot (Indexed 2,"victim"))
      DefineValue (PrimitiveValue "KIL",PrimitiveType "string")
      Completions (Indexed 3)
      Complete (Dot (Indexed 3,"equals"))
      Completions (Indexed 5)
      Complete (Apply (Indexed 5,"other",Indexed 4))
      Evaluate (Indexed 6)
      Abstract ([Indexed 2],Indexed 6)    
      Completions (Named "avia")
      Complete (Dot (Named "avia","filter"))
      Completions (Indexed 8)
      Complete (Apply (Indexed 8,"predicate",Indexed 7))
    ]
  let _prog = 
    [ DefineValue(PrimitiveValue 0, PrimitiveType "number")
      DefineValue(PrimitiveValue 10, PrimitiveType "number")
      Completions(Indexed 0)
      Complete(Dot(Indexed 0, "equals"))
      Completions(Indexed 2)
      Complete(Apply(Indexed 2, "other", Indexed 1))
      Abstract([Indexed 0], Indexed 3)
      DefineValue(PrimitiveValue 10, PrimitiveType "number")
      Completions(Indexed 4)
      Complete(Apply(Indexed 4, "arg0", Indexed 5))
      Evaluate(Indexed 3)
      Evaluate(Indexed 6)
    ]
  let code = prog |> List.fold (apply ctx) initial
  let state = 
    { Code = code; Program = prog; Context = ctx; CurrentFunction = None
      CurrentValue = None; CurrentName = None; CurrentReplace = None }
  createVirtualDomApp "out" state view update 
}