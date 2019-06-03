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
  | OperationValue of (Reference list * Reference) option * (Value list -> Value)
  | PrimitiveValue of obj
  | ObjectValue of ObjectValue

type Expr = 
  | External of string
  | Value of Value * Type
  | Member of Reference * string
  | Invocation of Reference * Reference list

and ObjectType = 
  abstract Members : (string * Type) list
  abstract Refine : Value -> ObjectType

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

type CompletionName = 
  | NamedCompletion of string
  | ParameterCompletion of (string * Reference) list

type Code = 
  { Source : list<Reference * Expr>
    Types : Map<Reference, Type>
    Values : Map<Reference, int * Value>
    Arguments : Map<string, Reference> option
    Counter : int
    Completions : (Reference * ((CompletionName * Completion) list)) option }

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
  let f v g = OperationValue(None, function 
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
  | Value(OperationValue(Some(rs, r), _), OperationType _) -> hash [ for r in r::rs -> hashCode code r ]
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
          | OperationValue(_, f), values ->
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

let substituteValueReference rold rnew value = 
  let subst r = if r = rold then rnew else r
  match value with 
  | OperationValue(Some(input, outputs), f) ->
      OperationValue(Some(List.map subst input, subst outputs), f)
  | _ -> value

let substituteReference rold rnew expr =
  let subst r = if r = rold then rnew else r
  match expr with 
  | Member(r, s) -> Member(subst r, s)
  | Value(v, t) -> Value(substituteValueReference rold rnew v, t)
  | Invocation(r, args) -> Invocation(subst r, List.map subst args)
  | e -> e

let addExpression ctx code nexpr =
  let ntyp =
    match nexpr with
    | Value(_, typ) -> typ
    | External(s) -> snd ctx.External.[s]
    | Invocation(op, args) ->
        match code.Types.[op] with 
        | OperationType(expectedArgs, res) ->
            let argTys = [ for a in args -> code.Types.[a] ]
            for (_, expected), actual in List.zip expectedArgs argTys do 
              if not (typesMatch expected actual) then
                failwithf "Type mismatch (or cannot compare): '%s' and '%s'" (string expected) (string actual)
            res
        | ty -> failwithf "Cannot invoke non-operation typed thing of type: %s" (string ty)    
    | Member(ref, name) ->
        let mems = code.Types.[ref] |> getMemberTypes
        match Seq.tryFind (fun (n, _) -> n = name) mems with
        | None -> failwithf "Member %s not found" name
        | Some(_, t) -> t
  { code with 
      Types = code.Types.Add(Indexed code.Counter, ntyp)
      Source = code.Source @ [ (Indexed code.Counter, nexpr) ]; Counter = code.Counter + 1 }

let rec apply ctx code interaction =
  // (fun res -> 
  //   printfn "\nAPPLIED: %A" interaction
  //   for r, e in res.Source do
  //     printfn "%A = %A" r e
  //     printfn "   Type = %A" res.Types.[r]
  //   res) <|
  match interaction with
  | Abstract(argRefs, res) ->
      let v = OperationValue(Some(argRefs, res), fun argVals ->
        let replaces = 
          List.zip argRefs argVals 
          |> List.map (fun (r, v) -> ReplaceValue(r, v, code.Types.[r]))
        let virtualCode = 
          List.append replaces [ Evaluate(res) ]
          |> List.fold (apply ctx) code
        virtualCode.Values.[res] |> snd )
      let argTys = 
        [ for i, r in Seq.indexed argRefs -> 
            sprintf "arg%d" i, code.Types.[r] ]
      let t = OperationType(argTys, code.Types.[res])
      addExpression ctx code (Value(v, t))

  | ReplaceValue(ref, v, t) ->
      let nexpr = Value(v, t)
      let nsource = code.Source |> List.map (fun (r, e) -> if r = ref then r, nexpr else r, e)
      { code with Source = nsource }

  | DefineValue(v, t) ->
      addExpression ctx code (Value(v, t))

  | Completions(ref) ->
      match code.Types.[ref] with 
      | OperationType(args, res) ->
          let appliedArgs = defaultArg code.Arguments Map.empty
          let args = args |> List.filter (fst >> appliedArgs.ContainsKey >> not)
          let srcTypes = [ for ref, _ in code.Source -> ref, code.Types.[ref] ]
          let compl = 
            [ for arg, argTy in args do
              for src, srcTy in srcTypes do
              //printf "Considering: %A = %A\n - Arg ty: %A\n - Src ty: %A\n - Matches: %A" arg src argTy srcTy (typesMatch argTy srcTy)
              if typesMatch argTy srcTy then
                yield ParameterCompletion([arg, src]), Apply(ref, arg, src) ]
          { code with Completions = Some(ref, compl) }
      | ty ->
          let compl = [ for m, _ in getMemberTypes ty -> NamedCompletion m, Dot(ref, m) ]
          { code with Completions = Some(ref, compl) }
  
  | Complete completion ->
      match completion with
      | Apply(opRef, arg, argRef) ->
          let actualArgs = defaultArg code.Arguments Map.empty |> Map.add arg argRef
          let actualSet = set [ for kvp in actualArgs -> kvp.Key ]
          match code.Types.[opRef] with 
          | OperationType(expectedArgs, res) when actualSet = set (List.map fst expectedArgs) ->
              addExpression ctx code
                (Invocation(opRef, [ for n, _ in expectedArgs -> actualArgs.[n]]))
          | _ -> 
              { code with Arguments = Some actualArgs }

      | Dot(ref, m) -> 
          addExpression ctx code (Member(ref, m))

  | Name(ref, name) ->
      let source = 
        [ for r, e in code.Source ->
            (if r = ref then Named name else r),
            substituteReference ref (Named name) e ] 
      let values = 
        [ for (KeyValue(r, (n, v))) in code.Values ->
            (if r = ref then Named name else r),
            (n, substituteValueReference r (Named name) v) ] |> Map.ofList
      let types = 
        [ for (KeyValue(r, t)) in code.Types ->
            (if r = ref then Named name else r), t ] |> Map.ofList
      { code with Source = source; Values = values; Types = types }

  | Evaluate(ref) ->
      let res, values = evaluate ctx code code.Values ref
      let newType = 
        match code.Types.[ref] with
        | ObjectType ot -> ObjectType(ot.Refine(res))
        | typ -> typ
      { code with Values = values; Types = code.Types.Add(ref, newType) }


// ------------------------------------------------------------------------------------------------
// User interface
// ------------------------------------------------------------------------------------------------

open Elmish
open Tbd.Html
open Fable.Core
open Fable.Import
open Fable.PowerPack

let renderTable data = 
  h?table ["class"=>"data"] [
    for row in data -> h?tr [] [
      for col in row -> h?td [] [ text (string col) ]
    ]
  ]


type CodeState = 
  { SelectedPath : Reference list option
    HighlightedPath : Reference list option }

type Model = 
  { Program : Program 
    Forward : Program
    Context : Context
    Code : Code
    Initial : Code

    CurrentFunction : Reference option
    CurrentReplace : (Reference * string) option
    CurrentValue : string option  
    CurrentName : (Reference * string) option 
    
    CodeState : CodeState
    }

type CodeEvent = 
  | Select of Reference list option
  | Highlight of Reference list option


type Event = 
  | Backward 
  | Forward

  | Interact of Interaction
  | Refresh

  | UpdateCurrentFunction of Reference option

  | FinishReplace
  | UpdateReplace of (Reference * string) option

  | FinishAddValue
  | UpdateAddValue of string option

  | FinishNaming 
  | UpdateName of (Reference * string) option
  
  | CodeEvent of CodeEvent

let interact op model =
  { model with Program = model.Program @ [op]; Code = apply model.Context model.Code op; Forward = [] }

let parse s = 
  match System.Int32.TryParse(s) with 
  | true, r -> PrimitiveType "number", PrimitiveValue r 
  | _ -> PrimitiveType "string", PrimitiveValue s

let updateCode state = function
  | Select path -> { state with SelectedPath = path }
  | Highlight path -> { state with HighlightedPath = path }

let update model = function
  | CodeEvent ce -> 
      { model with CodeState = updateCode model.CodeState ce }

  | Forward ->
      let prog = List.head model.Forward :: model.Program
      let fwd = List.tail model.Forward
      let code = apply model.Context model.Code (List.head model.Forward)
      { model with Program = prog; Code = code; Forward = fwd }
  | Backward ->
      let prog, last = match List.rev model.Program with x::xs -> List.rev xs, x | _ -> failwith "Cannot go back"
      let fwd = last :: model.Forward
      let code = prog |> List.fold (apply model.Context) model.Initial 
      printf "BEFORE: %d, AFTER: %d" model.Program.Length prog.Length
      { model with Program = prog; Forward = fwd; Code = code }

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
  h?table ["class"=>"sheet"] [
    h?tr [] [ for e in els -> h?td [ "class" => "cell cell-col" ] [ e ] ]
  ]
let rows els = 
  h?table ["class"=>"sheet"] [ 
    for e in els -> h?tr [] [ h?td [ "class" => "cell cell-row" ] [ e ] ] 
  ]

let renderPreview cls trigger (v:Value) = 
  h?div ["class" => cls ] [ 
    match v with 
    | OperationValue(_, v) -> yield text ("(Operation)")
    | ObjectValue v -> yield h?div [] [ text "Object:"; v.Preview(fun () -> trigger Refresh) ]
    | PrimitiveValue v -> yield text ("Primitive: " + string v) ]

let rec formatReference code ref = 
  match ref with 
  | Indexed n -> formatExpression code (find ref code.Source)
  | Named n -> n

and formatExpression code = function
  | External s -> sprintf "extern('%s')" s
  | Value(OperationValue _, _) -> "function"
  | Value(PrimitiveValue v, PrimitiveType "string") -> sprintf "value('%s')" (string v)
  | Value(PrimitiveValue v, _) -> sprintf "value(%s)" (string v)
  | Value(v, _) -> sprintf "value(%s)" (string v)
  | Member(ref, s) -> sprintf "%s.%s" (formatReference code ref) s
  | Invocation(ref, args) -> sprintf "%s(%s)" (formatReference code ref) (String.concat ", " (List.map (formatReference code) args))


let groupSource source = 
  let refs =  
    [ for r, e in source do
        match e with Invocation(t, _) | Member(t, _) -> yield t, r | _ -> () ] 
    |> List.groupBy fst 
    |> List.choose (function (k, [_, it]) -> Some(k, it) | _ -> None)
    |> dict

  let rec follow r = seq {
    yield r
    if refs.ContainsKey r then 
      yield! follow refs.[r] }

  let chains = 
    [ for r, _ in source -> r, List.ofSeq (follow r) ]
    |> List.sortByDescending (snd >> List.length)
    |> List.fold (fun (visited, res) (s, chain) ->
        if Set.contains s visited then visited, res
        else Set.union visited (set chain), (s, chain)::res) (Set.empty, [])
    |> snd
    |> List.filter (fun (_, g) -> List.length g > 1)
    |> dict
  
  let inChains = set (Seq.concat chains.Values)
  let sourceLookup = dict source

  [ for r, _ in source do
      if chains.ContainsKey r then yield chains.[r]
      elif Set.contains r inChains then ()
      else yield [r] ]
  |> List.map (List.map (fun r -> r, sourceLookup.[r]))


let getValue state k = 
  state.Code.Values.TryFind(k) 
  |> Option.bind (fun (h, v) -> 
    if hashCode state.Code k = h then Some v else None)

let renderSheet trigger state = 
  cols [ 
    for g in groupSource state.Code.Source -> rows [
      for k, v in g -> h?div [] [
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
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateReplace(Some(k, ""))) ] [ text "replace" ]
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
            yield h?br [] []
        | _ ->
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateName(Some(k, ""))) ] [ text "name" ]
            yield h?br [] []

        match state.CurrentFunction with
        | Some ref when ref = k -> 
            yield rows [
              for inp in getInputs state.Code ref ->
                h?button ["click" =!> fun _ _ -> trigger(Interact(Abstract([inp], k)))] [ text ("taking " + string inp) ]
            ]
        | _ -> 
          yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateCurrentFunction(Some(k))) ] [ text "function" ]
          yield h?br [] []

        match state.Code.Completions with
        | Some(ref, compl) when k = ref && List.isEmpty compl ->
            yield rows [ text "(no completions)" ]
        | Some(ref, compl) when k = ref ->
            yield rows [
              let formatCompl = function
                | NamedCompletion n -> n
                | ParameterCompletion pars -> [ for a, r in pars -> sprintf "%s=%A" a r ] |> String.concat ", "
              for n, c in compl -> h?button ["click" =!> fun _ _ -> trigger(Interact(Complete c)) ] [ text (formatCompl n) ]
            ]
        | _ ->
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(Interact(Completions k)) ] [ text "completions" ]
            yield h?br [] []

        match getValue state k with
        | Some(v) ->
            yield renderPreview "preview" trigger v
        | None -> 
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(Interact(Evaluate k)) ] [ text "evaluate" ]
            yield h?br [] []      
        ]
      ]
    yield h?div [] [
      if state.CurrentValue = None then
        yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateAddValue (Some "")) ] [ text "Add value" ]
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

let rec collectReferences code e = seq {
  match e with 
  | Member(r, _) -> 
      yield r
      yield! collectReferences code (find r code)
  | Invocation(r, rs) -> 
      for r in r::rs do
        yield r
        yield! collectReferences code (find r code) 
  | _ -> () }

type RenderContext = 
  { Trigger : Event -> unit 
    Code : (Reference * Expr) list
    AllState : Model
    State : CodeState
    Variables : Map<Reference, string> }

let rec formatReferencedExpr ctx ref = 
  match ref with 
  | _ when ctx.Variables.ContainsKey ref -> ctx.Variables.[ref]
  | Named n -> n
  | _ -> 
  match find ref ctx.Code with
  | External(s) -> sprintf "external(%s)" s
  | Value(PrimitiveValue v, PrimitiveType "string") -> sprintf "\"%s\"" (string v)
  | Value(PrimitiveValue v, _) -> sprintf "%s" (string v)
  | Value(ObjectValue o, _) -> string o
  | Value(OperationValue(Some(inputs, output), _), _) -> 
      let vars = 
        if inputs.Length = 1 then Seq.zip inputs ["v"] 
        else Seq.indexed inputs |> Seq.map (fun (i, v) -> v, sprintf "v%d" i) 
      String.concat "" [
        yield "fun "
        for _, n in vars -> n + " "
        yield "-> "
        let ctx = { ctx with Variables = Map.ofSeq vars }
        yield formatReferencedExpr ctx output
      ]
  | Value(OperationValue(None, _), _) -> "(built-in function)"
  | Member(r, s) -> formatReferencedExpr ctx r + "." + s
  | Invocation(r, rs) -> 
      String.concat "" [ 
        yield formatReferencedExpr ctx r
        yield "("
        for i, r in Seq.indexed rs do
          if i <> 0 then yield ", "
          yield formatReferencedExpr ctx r
        yield ")"
      ]

let pathStarts path pathOpt = 
  match path, pathOpt with 
  | p1::_, Some(p2::_) -> p1 = p2
  | _ -> false

let renderSelectableBox ctx (path, ref) extras body =
  h?span [] [ 
    yield h?span 
      [ yield "class" => 
          if pathStarts path ctx.State.SelectedPath then "expr selected" 
          elif pathStarts path ctx.State.HighlightedPath then "expr highlighted" 
          else "expr"
        yield "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger (CodeEvent(Select(Some path))) 
        yield "mousemove" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger (CodeEvent(Highlight(Some path)))
        yield! extras
      ] [ body ]
    if pathStarts path ctx.State.SelectedPath then
      yield h?div [ "style" => "display:inline-block" ] [
        yield h?button [ 
          "class" => "plus"
          "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(Interact(Completions ref))
        ] [ text "+" ]        
        match ctx.AllState.Code.Completions with
        | Some(k, compl) when Some path = ctx.State.SelectedPath && k = ref ->
            yield h?div [ "class" => "completions" ] [
              match ctx.AllState.CurrentName with
              | Some(k, n) when ref = k ->
                  yield h?input [ 
                    "value" => n
                    "input" =!> fun e _ -> ctx.Trigger(UpdateName(Some(ref, unbox<Browser.HTMLInputElement>(e).value))) 
                    "click" =!> fun _ e -> e.cancelBubble <- true
                    "keydown" =!> fun _ k -> 
                      match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
                      | 13 -> ctx.Trigger(FinishNaming)
                      | 27 -> ctx.Trigger(UpdateName None)
                      | _ -> ()
                    ] []
              | _ ->
              match ctx.AllState.CurrentFunction with
              | Some k when ref = k -> 
                  for inp in getInputs ctx.AllState.Code ref ->
                    h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(Interact(Abstract([inp], k)))] [ text ("taking " + formatReferencedExpr ctx inp) ]
              | _ -> 
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCurrentFunction(Some(k))) ] [ text "function" ]
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateName(Some(k, ""))) ] [ text "name" ]              
                if not (List.isEmpty compl) then
                  yield h?hr [] []
                  let formatCompl = function
                    | NamedCompletion n -> n
                    | ParameterCompletion pars -> [ for n, r in pars -> sprintf "%s = %s" n (formatReferencedExpr ctx r) ] |> String.concat ", "
                  for n, c in compl -> h?a ["href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(Interact(Complete c)) ] [ text (formatCompl n) ]
            ]
        | _ -> () 
      ]
  ]

let rec renderReferencedExpression ctx (path, ref) = 
  match ref, ctx.AllState.CurrentReplace with 
  | _ when ctx.Variables.ContainsKey ref -> text (ctx.Variables.[ref])
  | _, Some(r, v) when r = ref ->
      h?input [ 
        "input" =!> fun e _ -> ctx.Trigger(UpdateReplace(Some(ref, unbox<Browser.HTMLInputElement>(e).value))) 
        "value" => v
        "keydown" =!> fun _ k -> 
          match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
          | 13 -> ctx.Trigger(FinishReplace)
          | 27 -> ctx.Trigger(UpdateReplace None)
          | _ -> ()
        ] []
  | Named n, _ 
        when collectReferences ctx.Code (find ref ctx.Code) 
             |> Seq.exists ctx.Variables.ContainsKey |> not -> 
      renderSelectableBox ctx (path, ref) [] (text n)
  | r, _ -> renderExpression ctx (path, ref) (find r ctx.Code)

and renderExpression (ctx:RenderContext) (path, ref) expr = 
  let rsb = renderSelectableBox ctx (path, ref) []
  let rsbe = renderSelectableBox ctx (path, ref) 
  match expr with 
  | External(s) -> text (sprintf "external(%s)" s) |> rsb
  | Value(PrimitiveValue v, PrimitiveType "string") -> 
      text (sprintf "\"%s\"" (string v)) |> rsbe [
        "dblclick" =!> fun _ _ -> ctx.Trigger(UpdateReplace(Some(ref, string v)))
      ]
  | Value(PrimitiveValue v, _) -> 
      text (sprintf "%s" (string v)) |> rsbe [
        "dblclick" =!> fun _ e -> ctx.Trigger(UpdateReplace(Some(ref, string v)))
      ]
  | Value(ObjectValue o, _) -> 
      text (string o) |> rsb

  | Value(OperationValue(Some(inputs, output), _), _) -> 
      let vars = 
        if inputs.Length = 1 then Seq.zip inputs ["v"] 
        else Seq.indexed inputs |> Seq.map (fun (i, v) -> v, sprintf "v%d" i) 
      h?span [] [ 
        yield text "fun "
        for _, n in vars -> text (n + " ")
        yield text "-> "
        let ctx = { ctx with Variables = Map.ofSeq vars }
        yield renderExpression ctx (output::path, output) (find output ctx.Code)        
      ] |> rsb
  | Value(OperationValue(None, _), _) -> text ("(built-in function)") |> rsb
  | Member(r, s) -> 
      h?span [] [ 
        renderReferencedExpression ctx (r::path, r)
        text "."
        text s
      ] |> rsb
  | Invocation(r, rs) -> 
      h?span [] [ 
        yield renderReferencedExpression ctx (r::path, r)
        yield h?span [] [ 
          yield text "("
          for i, r in Seq.indexed rs do
            if i <> 0 then yield text ", "
            yield renderReferencedExpression ctx (r::path, r)
          yield text ")"
        ]
      ] |> rsb

let renderText trigger (state:Model) = 
  let code = state.Code.Source
  let allRefs = code |> Seq.collect (snd >> collectReferences code) |> set
  let ctx = { Code = state.Code.Source; Trigger = trigger; Variables = Map.empty; AllState = state; State = state.CodeState }

  let code = 
    h?div 
      [ "class" => "code" 
        "click" =!> fun _ e -> e.cancelBubble <- true; trigger (CodeEvent(Select(None))) 
        "mousemove" =!> fun _ e -> e.cancelBubble <- true; trigger (CodeEvent(Highlight(None)))
        "mouseout" =!> fun _ e -> e.cancelBubble <- true; trigger (CodeEvent(Highlight(None)))
      ] [
        for ref, _ in code ->
          h?div [] [
            match ref, allRefs.Contains ref with 
            | Named n, _ ->
                yield h?span [ "class" => "let" ] [ text ("let " + n + " = ") ]
                //yield renderReferencedExpression ctx ref 
                yield renderExpression ctx ([ref], ref) (find ref ctx.Code)
            | Indexed n, false ->
                yield h?span [ "class" => "let" ] [ text (sprintf "do[%d]" n) ]
                yield renderReferencedExpression ctx ([ref], ref) 
            | _ -> ()
          ]
        yield h?div [] [
          yield h?span [ "class" => "let" ] [ text "do" ]
          if state.CurrentValue = None then
            yield h?button [ "class" => "value"; "click" =!> fun _ _ -> trigger(UpdateAddValue (Some "")) ] [ text "add value" ]
          else
            yield h?input [ 
              "input" =!> fun e _ -> trigger(UpdateAddValue(Some(unbox<Browser.HTMLInputElement>(e).value))) 
              "keydown" =!> fun _ k -> 
                match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
                | 13 -> trigger(FinishAddValue)
                | 27 -> trigger(UpdateAddValue None)
                | _ -> () ] []
        ]   
      ]
  let preview = 
    h?div [] [ 
      match ctx.State.HighlightedPath, ctx.State.SelectedPath with
      | Some (ref::_), _ 
      | _, Some (ref::_) ->
          match getValue ctx.AllState ref with
          | Some(v) ->
              yield renderPreview "bigpreview" trigger v
          | None -> 
              yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(Interact(Evaluate ref)) ] [ text "evaluate" ]
      | _ -> ()
    ]

  h?table ["class" => "split"] [ h?tr [] [ h?td [] [ code ]; h?td [] [ preview ] ] ]
(*
  { Source : list<Reference * Expr>
    Values : Map<Reference, int * Value>
    Arguments : Map<string, Reference> option
    Counter : int
    Completions : (Reference * ((string * Completion) list)) option }
  []
*)

let view trigger state =
  //Browser.console.log("PROGRAM")
  //for p in state.Program do Browser.console.log(" * ", string p)
  h?div [] [
    h?div [] [
      if not (List.isEmpty state.Program) then
        yield h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger Backward] [ text "<- Back" ] 
      yield text (sprintf " (%d past interactions, %d forward) " state.Program.Length state.Forward.Length)
      if not (List.isEmpty state.Forward) then
        yield h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger Forward ] [ text "Forward ->" ] 
    ]
    renderText trigger state
    //renderSheet trigger state 
  ]


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
    member x.Refine _ = x
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
        if m = "at" then OperationValue(None, function  
          | [PrimitiveValue n] -> 
              let _, v, _ = (Array.item (unbox n) rows) in v 
          | _ -> failwith "dataArray.at: Invalid index")

        elif m = "filter" then OperationValue(None, function 
          | [OperationValue(_, f)] -> 
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
        member x.Refine _ = x
        member x.Members = 
          let _, _, mt = Array.item 0 rows
          [ yield "at", OperationType(["index", PrimitiveType "number"], mt)
            yield "filter", OperationType(["predicate", OperationType(["row", mt], PrimitiveType "bool")], t)
            //for i, (_, t) in Seq.indexed rows -> string i, t 
            ] } |> ObjectType
  return v rows, t }

let test = 
  { new ObjectValue with
      member x.Hash = 123
      member x.Preview _ = h?p [] [ text "Hi there" ] 
      member x.Lookup m = if m = "test" then PrimitiveValue(42) else failwith "lookup" } |> ObjectValue,
  { new ObjectType with
      member x.Refine v = 
        printfn "%A" v
        { new ObjectType with
            member x.Refine _ = x
            member x.Members = [ "test", PrimitiveType "number"] }
      member x.Members = [] } |> ObjectType

let initial = 
  { Completions = None 
    Arguments = None
    Types = Map.empty
    Source = [ ]
    Values = Map.empty
    Counter = 0 }

Async.StartImmediate <| async {
  try
    let! avia = dataArray "data/avia.csv"
    let! rail = dataArray "data/rail.csv"
    let external = ["avia", avia; "rail", rail; "test", test]
    let ctx = { External = Map.ofList external }
    let initial = 
      { initial with 
          Source = [ for n, _ in external -> Named n, External n ]
          Types = Map.ofSeq [ for n, (_, t) in external -> Named n, t ] }

    let prog = []
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
    let code = prog |> List.fold (apply ctx) initial
    let state = 
      { Initial = initial; Code = code; Program = prog; Context = ctx; CurrentFunction = None; Forward = [];
        CurrentValue = None; CurrentName = None; CurrentReplace = None 
        CodeState = { SelectedPath = None; HighlightedPath = None } }
    createVirtualDomApp "out" state view update 
  with e ->
    Browser.console.error(e)
}