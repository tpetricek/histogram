module App

// ------------------------------------------------------------------------------------------------
// Types
// ------------------------------------------------------------------------------------------------

type Reference =
  | Named of string
  | Indexed of int

type PreviewContext = 
  { Reference : Reference 
    Interact : Interaction -> Async<Reference option>
    Select : Reference -> unit }

and ObjectValue =
  abstract Lookup : string -> Value
  abstract Preview : PreviewContext -> string * Tbd.Html.DomNode option
  abstract Hash : int

and Value =
  | OperationValue of (Reference list * Reference) option * (Value list -> Async<Value>)
  | PrimitiveValue of obj
  | ObjectValue of ObjectValue

and Expr =
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

and Completion =
  | Dot of Reference * string
  | Apply of Reference * string * Reference

and Interaction =
  | Complete of Completion
  | Name of Reference * string
  | Evaluate of Reference
  | Abstract of Reference list * Reference
  | DefineValue of Value * Type
  | DefineExternal of string
  | ReplaceValue of Reference * Value * Type

type CompletionName =
  | NamedCompletion of string
  | ParameterCompletion of (string * Reference) list

type Code =
  { External : Map<string, Value * Type>
    Source : list<Reference * Expr>
    Values : Map<Reference, int * Value>
    Arguments : Map<string, Reference> option
    Counter : int }

type Program = list<Interaction>

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
  | OperationType _
  | PrimitiveType _ -> failwithf "getMemberTypes: Cannot get members on %s" (string ty)

let getMemberValue m v =
  let f v g = OperationValue(None, function
    | [PrimitiveValue other] -> async.Return(PrimitiveValue(g (unbox v) (unbox other)))
    | _ -> failwith "getMemberValue: Bad arguments")
  match v with
  | ObjectValue v -> v.Lookup m
  | PrimitiveValue v when m = "equals" -> f v (fun a b -> a = b)
  | PrimitiveValue v when m = "not equals" -> f v (fun a b -> a <> b)
  | PrimitiveValue v when m = "and" -> f v (fun a b -> a && b)
  | PrimitiveValue v when m = "or" -> f v (fun a b -> a || b)
  | _ -> failwithf "Cannot access member '%s' of a primitive value" m

let rec typeCompatibleWith expected actual =
  match expected, actual with
  | ObjectType(o1), ObjectType(o2) ->
      // TODO: Structural typing for objects with subtyping (!)
      let o2members = dict o2.Members
      o1.Members |> List.forall (fun (n, t) ->
        o2members.ContainsKey n && typeCompatibleWith t o2members.[n])
  | PrimitiveType t1, PrimitiveType t2 -> t1 = t2
  | OperationType(args1, res1), OperationType(args2, res2) ->
      typeCompatibleWith res1 res2 &&
      List.forall2 (fun a1 a2 -> typeCompatibleWith (snd a1) (snd a2)) args1 args2
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

let rec formatType depth typ =
  match typ with
  | ObjectType _ when depth > 3 -> "record"
  | OperationType _ when depth > 3 -> "operation"
  | PrimitiveType p -> p
  | ObjectType(ot) -> sprintf "{ %s }" (String.concat ", " [for m, t in Seq.truncate 5 ot.Members -> m + ":" + formatType (depth+1) t])
  | OperationType(args, res) -> sprintf "(%s) -> %s" (String.concat ", " [for m, t in args -> m + ":" + formatType (depth+1) t]) (formatType (depth+1) res)

let rec evaluateExpr code values ref = async {
  match find ref code.Source with
  | Value(v, _) -> return v, values

  | Invocation(refInst, args) ->
      let! inst = evaluate code values refInst
      match inst with
      | OperationValue(_, f), values ->
          let evaluatedArgs = ResizeArray<_>()
          let mutable currentValues = values
          for arg in args do
            let! arg, values = evaluate code currentValues arg
            currentValues <- values
            evaluatedArgs.Add(arg)
          let! res = f (List.ofSeq evaluatedArgs)
          return res, values
      | v, _ ->
          return failwithf "evaluate: Cannot invoke non-operation-valued thing at %s: %s" (string ref) (string v)

  | External e ->
      return fst (code.External.[e]), values

  | Member(inst, m) ->
      let! v, values = evaluate code values inst
      return getMemberValue m v, values }

and evaluate code (values:Map<Reference, int * Value>) ref : Async<_ * _> = async {
  match Map.tryFind ref values with
  | Some(h, v) when hashCode code ref = h -> return v, values
  | _ ->
      let! v, values = evaluateExpr code values ref
      return v, Map.add ref (hashCode code ref, v) values }

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

let rec typeCheckExpr code expr =
  match expr with
  | Value(_, typ) -> typ
  | External(s) -> snd code.External.[s]
  | Invocation(op, args) ->
        match typeCheck code op with
        | OperationType(expectedArgs, res) ->
            let argTys = [ for a in args -> typeCheck code a ]
            for (_, expected), actual in List.zip expectedArgs argTys do
              if not (typeCompatibleWith expected actual) then
                failwithf "Type mismatch (or cannot compare): '%s' and '%s'" (string expected) (string actual)
            res
        | ty -> failwithf "Cannot invoke non-operation typed thing of type: %s" (string ty)
  | Member(ref, name) ->
      let objTy = typeCheck code ref
      let mems = getMemberTypes objTy
      match Seq.tryFind (fun (n, _) -> n = name) mems with
      | None -> failwithf "Member %s not found" name
      | Some(_, t) -> t

and typeCheck code (ref:Reference) =
  match typeCheckExpr code (find ref code.Source) with
  | ObjectType(ot) when code.Values.ContainsKey ref ->
      ObjectType(ot.Refine(snd code.Values.[ref]))
  | typ -> typ

let addExpression code nexpr =
  let ref = Indexed code.Counter
  let newSource = code.Source @ [ (ref, nexpr) ]
  Some ref, { code with Source = newSource; Counter = code.Counter + 1 }

let getCompletions code ref =
  match typeCheck code ref with
  | OperationType(args, res) ->
      let appliedArgs = defaultArg code.Arguments Map.empty
      let args = args |> List.filter (fst >> appliedArgs.ContainsKey >> not)
      let srcTypes = [ for ref, _ in code.Source -> ref, typeCheck code ref ]
      [ for arg, argTy in args do
        for src, srcTy in srcTypes do
        if typeCompatibleWith argTy srcTy then
          yield ParameterCompletion([arg, src]), Apply(ref, arg, src) ]
  | ty ->
      [ for m, _ in getMemberTypes ty -> NamedCompletion m, Dot(ref, m) ]

let rec apply code interaction = async {
  // (fun res ->
  //   printfn "\nAPPLIED: %A" interaction
  //   for r, e in res.Source do
  //     printfn "%A = %A" r e
  //     printfn "   Type = %A" res.Types.[r]
  //   res) <|
  match interaction with
  | Abstract(argRefs, res) ->
      let v = OperationValue(Some(argRefs, res), fun argVals -> async {
        let replaces =
          List.zip argRefs argVals
          |> List.map (fun (r, v) -> ReplaceValue(r, v, typeCheck code r))
        let mutable virtualCode = code
        for interaction in List.append replaces [ Evaluate(res) ] do
          let! _, vc = apply virtualCode interaction
          virtualCode <- vc
        return virtualCode.Values.[res] |> snd })
      let argTys =
        [ for i, r in Seq.indexed argRefs ->
            sprintf "arg%d" i,  typeCheck code r ]
      let t = OperationType(argTys,  typeCheck code res)
      return addExpression code (Value(v, t))

  | ReplaceValue(ref, v, t) ->
      let nexpr = Value(v, t)
      let nsource = code.Source |> List.map (fun (r, e) -> if r = ref then r, nexpr else r, e)
      return None, { code with Source = nsource }

  | DefineValue(v, t) ->
      return addExpression code (Value(v, t))

  | DefineExternal(s) ->
      return addExpression code (External(s))

  | Complete completion ->
      match completion with
      | Apply(opRef, arg, argRef) ->
          let actualArgs = defaultArg code.Arguments Map.empty |> Map.add arg argRef
          let actualSet = set [ for kvp in actualArgs -> kvp.Key ]
          match typeCheck code opRef with
          | OperationType(expectedArgs, res) when actualSet = set (List.map fst expectedArgs) ->
              return addExpression code
                (Invocation(opRef, [ for n, _ in expectedArgs -> actualArgs.[n]]))
          | _ ->
              return failwith "Cannot apply Apply completion on non-operation"

      | Dot(ref, m) ->
          return addExpression code (Member(ref, m))

  | Name(ref, name) ->
      let source =
        [ for r, e in code.Source ->
            (if r = ref then Named name else r),
            substituteReference ref (Named name) e ]
      let values =
        [ for (KeyValue(r, (n, v))) in code.Values ->
            (if r = ref then Named name else r),
            (n, substituteValueReference r (Named name) v) ] |> Map.ofList
      return Some(Named name), { code with Source = source; Values = values }

  | Evaluate(ref) ->
      let! _, values = evaluate code code.Values ref
      return None, { code with Values = values } }


// ------------------------------------------------------------------------------------------------
// User interface
// ------------------------------------------------------------------------------------------------

open Elmish
open Tbd.Html
open Tbd.Compost
open Fable.Core
open Fable.Import
open Fable.PowerPack
open Tbd

let renderTable headers data =
  h?div ["class"=>"table-container"] [
    h?table ["class"=>"data"] [
      h?thead [] [
        h?tr [] [
          for hd in headers -> h?th [] (hd)
        ]
      ]
      h?tbody [] [
        for row in data -> h?tr [] [
          for col in row -> h?td [] col
        ]
      ]
    ]
  ]


type Model =
  { Program : Program
    Forward : Program
    Code : Code
    Initial : Code

    CurrentCompletions : (Reference * ((CompletionName * Completion) list)) option
    CurrentFunction : Reference option
    CurrentReplace : (Reference * string) option
    CurrentValue : string option
    CurrentName : (Reference * string) option

    SelectedPath : Reference list option
    HighlightedPath : Reference list option
    SelectedMenuItem : int option 

    Caption : (int * string) option
    Modified : bool }

type Event =
  | Backward
  | Forward

  | Caption of int * string
  | Interact of Interaction * (Reference option -> unit)
  //| Refresh

  | UpdateCompletions of Reference option

  | UpdateCurrentFunction of Reference option

  | FinishReplace
  | UpdateReplace of (Reference * string) option

  | FinishAddValue
  | UpdateAddValue of string option

  | FinishNaming
  | UpdateName of (Reference * string) option

  | Select of Reference list option
  | Highlight of Reference list option
  | SelectMenu of int option
 
let justInteract i = Interact(i, ignore)

let interact trigger op cont model = async {
  let! ref, code = apply model.Code op
  match cont with 
  | Some cont -> cont ref
  | _ -> ()
  return { model with Program = model.Program @ [op]; Code = code; Forward = []; CurrentFunction = None } }

let parse s =
  match System.Int32.TryParse(s) with
  | true, r -> PrimitiveType "number", PrimitiveValue r
  | _ when s.[0] = '\"' && s.[s.Length-1] = '\"' -> PrimitiveType "string", PrimitiveValue (s.[1 .. s.Length-2]) 
  | _ -> PrimitiveType "string", PrimitiveValue s

let update trigger model evt = async {
  let interact = interact trigger
  match evt with
  | Caption(n, s) -> 
      return { model with Caption = Some(n, s) }

  | Select path -> return { model with SelectedPath = path; SelectedMenuItem = None }
  | Highlight path -> return { model with HighlightedPath = path }
  | SelectMenu item -> return { model with SelectedMenuItem = item }

  | Forward ->
      let prog = List.head model.Forward :: model.Program
      let fwd = List.tail model.Forward
      let! _, code = apply model.Code (List.head model.Forward)
      return { model with Program = prog; Code = code; Forward = fwd; Modified = true }
  | Backward ->
      let prog, last = match List.rev model.Program with x::xs -> List.rev xs, x | _ -> failwith "Cannot go back"
      let fwd = last :: model.Forward
      let mutable code = model.Initial
      for op in prog do
        let! _, c = apply code op
        code <- c
      return { 
        Initial = model.Initial; Caption = model.Caption; Modified = true
        Program = prog; Forward = fwd; Code = code;
        CurrentCompletions = None; CurrentFunction = None; CurrentReplace = None;
        CurrentValue = None; CurrentName = None; SelectedPath = None; 
        HighlightedPath = None; SelectedMenuItem = None }

  //| Refresh -> return model

  | UpdateCompletions ref ->
      let completions =
        if ref = Some(Indexed -1) then Some(Indexed -1, [])
        else ref |> Option.map (fun ref -> ref, getCompletions model.Code ref)
      return { model with CurrentCompletions = completions; Modified = true }

  | UpdateCurrentFunction f ->
      return { model with CurrentFunction = f; Modified = true }

  | UpdateReplace r ->
      return { model with CurrentReplace = r; Modified = true }
  | FinishReplace ->
      let ref, s = model.CurrentReplace.Value
      let t, v = parse s
      return! { model with CurrentReplace = None; Modified = true } |> interact (ReplaceValue(ref, v, t)) None

  | UpdateAddValue s ->
      return { model with CurrentValue = s; Modified = true }
  | FinishAddValue ->
      let t, v = parse (defaultArg model.CurrentValue "")
      return! { model with CurrentValue = None; Modified = true; CurrentCompletions = None } |> interact (DefineValue(v, t)) None

  | UpdateName(rn) ->
      return { model with CurrentName = rn; Modified = true }
  | FinishNaming ->
      match model.CurrentName with
      | Some(ref, n) -> return! { model with CurrentName = None; Modified = true } |> interact (Name(ref, n)) None
      | _ -> return failwith "Cannot finish naming when current name is none"

  | Interact(i, cont) ->
      return! { model with CurrentCompletions = None; Modified = true } |> interact i (Some cont) }

let cols cls els =
  h?table ["class"=>cls] [
    h?tr [] [ for e in els -> h?td [ "class" => "cell cell-col" ] [ e ] ]
  ]
let rows cls els =
  h?table ["class"=>cls] [
    for e in els -> h?tr [] [ h?td [ "class" => "cell cell-row" ] [ e ] ]
  ]

let getPreview ref trigger (v:Value) (typ:Type) =
  match v, typ with
  | OperationValue _, _ -> "Block is an operation " + formatType 3 typ, None
  | PrimitiveValue v, PrimitiveType "string" -> "Block is a text '" + string v + "'", None
  | PrimitiveValue v, PrimitiveType "number" -> "Block is a number " + string v, None
  | PrimitiveValue v, _ -> "Block is a primitive value '" + string v + "'", None
  | ObjectValue v, _ -> 
      let ctx = 
        { Reference = ref
          Interact = fun i -> Async.FromContinuations(fun (cont, _, _) -> 
            trigger (Interact(i, cont)) )
          Select = fun ref -> trigger (Select (Some [ref]))
        }
      v.Preview(ctx)

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

  let grid = 
    [| for r, _ in source do
        if chains.ContainsKey r then yield chains.[r] |> Array.ofList
        elif Set.contains r inChains then ()
        else yield [| r |] |]
    |> Array.map (Array.map (fun r -> r, sourceLookup.[r]))

  let primitives, chains = 
    grid |> Array.partition (function
      | [| ref, Value _ |] -> true
      | _ -> false)
  if primitives.Length = 0 then chains
  else Array.append [| Array.concat primitives |] chains

let getValue state k =
  state.Code.Values.TryFind(k)
  |> Option.bind (fun (h, v) ->
    if hashCode state.Code k = h then Some v else None)

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
    State : Model
    Variables : Map<Reference, string> }

let rec formatReferencedExpr ctx ref =
  match ref with
  | _ when ctx.Variables.ContainsKey ref -> ctx.Variables.[ref]
  | Named n -> n
  | _ ->
  match find ref ctx.Code with
  | External(s) -> sprintf "%s" s
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

let renderCompletions (ctx:RenderContext) items =
  h?div 
    [ "class" => "completions" 
      "mouseleave" =!> fun _ e -> ctx.Trigger(SelectMenu None) ]
    [ for i, it in Seq.indexed items ->
        match it with
        | Element(ns, "a", attrs, children, render) ->
            let extras = [|
              if Some i = ctx.State.SelectedMenuItem  then yield "class" => "selected"
              yield "mouseover" =!> fun _ _ -> ctx.Trigger(SelectMenu(Some i))
            |]
            Element(ns, "a", Array.append extras attrs, children, render)
        | _ -> it ]

let renderSelectableBox ctx (path, ref) extras body =
  h?span [ 
    "mousemove" =!> fun _ e -> e.cancelBubble <- true
  ] [
    yield h?span
      [ yield "class" =>
          if pathStarts path ctx.State.SelectedPath then "expr selected"
          elif pathStarts path ctx.State.HighlightedPath then "expr highlighted"
          else "expr"
        yield "dblclick" =!> fun _ e ->
          e.cancelBubble <- true
          Browser.window.getSelection().removeAllRanges()
          ctx.Trigger(justInteract(Evaluate ref)) 
        yield "click" =!> fun _ e ->
          e.cancelBubble <- true
          if ctx.State.SelectedPath <> Some path then ctx.Trigger (Select(Some path))
        yield "mousemove" =!> fun _ e ->
          e.cancelBubble <- true
          if ctx.State.HighlightedPath <> Some path then ctx.Trigger (Highlight(Some path))
        yield! extras
      ] [
        body
        //h?ul ["style"=>"font-size:50%"] [
        //  yield h?li [] [ text (sprintf "[%s]" (formatType 0 (typeCheck ctx.State.Code ref))) ]
        //]
      ]
    if pathStarts path ctx.State.SelectedPath then
      yield h?div [ "style" => "display:inline-block" ] [
        yield h?button [
          "class" => "plus"
          "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCompletions(Some ref))
        ] [ text "+" ]
        match ctx.State.CurrentCompletions with
        | Some(k, compl) when Some path = ctx.State.SelectedPath && k = ref ->
            yield renderCompletions ctx [
              match ctx.State.CurrentName with
              | Some(k, n) when ref = k ->
                  yield h?span [] [ text "enter variable name" ]
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
              match ctx.State.CurrentFunction with
              | Some k when ref = k ->
                  for inp in getInputs ctx.State.Code ref ->
                    h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(Abstract([inp], k)))] [ text ("taking " + formatReferencedExpr ctx inp) ]
              | _ ->
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCurrentFunction(Some(k))) ] [ text "function" ]
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateName(Some(k, ""))) ] [ text "name" ]
                if not (List.isEmpty compl) then
                  yield h?hr [] []
                  let formatCompl = function
                    | NamedCompletion n -> n
                    | ParameterCompletion pars -> [ for n, r in pars -> sprintf "%s = %s" n (formatReferencedExpr ctx r) ] |> String.concat ", "
                  for n, c in compl -> h?a ["href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(Complete c)) ] [ text (formatCompl n) ]
            ]
        | _ -> ()
      ]
  ]

let rec renderReferencedExpression ctx (path, ref) : _ list =
  [ match ref, ctx.State.CurrentReplace with
    | _ when ctx.Variables.ContainsKey ref -> yield text (ctx.Variables.[ref])
    | _, Some(r, v) when r = ref ->
        yield h?input [
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
        yield renderSelectableBox ctx (path, ref) [] (text n)
    | r, _ -> yield! renderExpression ctx (path, ref) (find r ctx.Code) ]

and renderExpression (ctx:RenderContext) (path, ref) expr : _ list =
  [ let rsb = renderSelectableBox ctx (path, ref) []
    let rsbe = renderSelectableBox ctx (path, ref)
    match expr with
    | External(s) -> yield text (sprintf "%s" s) |> rsb
    | Value(PrimitiveValue v, PrimitiveType "string") ->
        yield text (sprintf "\"%s\"" (string v)) |> rsbe [
          "dblclick" =!> fun _ _ -> ctx.Trigger(UpdateReplace(Some(ref, string v)))
        ]
    | Value(PrimitiveValue v, _) ->
        yield text (sprintf "%s" (string v)) |> rsbe [
          "dblclick" =!> fun _ e -> ctx.Trigger(UpdateReplace(Some(ref, string v)))
        ]
    | Value(ObjectValue o, _) ->
        yield text (string o) |> rsb

    | Value(OperationValue(Some(inputs, output), _), _) ->
        let vars =
          if inputs.Length = 1 then Seq.zip inputs ["v"]
          else Seq.indexed inputs |> Seq.map (fun (i, v) -> v, sprintf "v%d" i)
        yield h?span [] [
          yield text "fun "
          for _, n in vars -> text (n + " ")
          yield text "-> " ] |> rsb
        let ctx = { ctx with Variables = Map.ofSeq vars }
        yield! renderExpression ctx (output::path, output) (find output ctx.Code)

    | Value(OperationValue(None, _), _) ->
        yield text ("(built-in function)") |> rsb
    | Member(r, s) ->
        yield! renderReferencedExpression ctx (r::path, r)
        yield text "."
        yield text s |> rsb

    | Invocation(r, rs) ->
        let it = renderReferencedExpression ctx (r::path, r) |> List.rev
        let last = List.head it
        let rest = List.rev (List.tail it)
        yield! rest
        yield h?span [] [
          yield last
          yield text "("
          for i, r in Seq.indexed rs do
            if i <> 0 then yield text ", "
            yield! renderReferencedExpression ctx (r::path, r)
          yield text ")"
        ] |> rsb ]

let printPathReference (reverse:System.Collections.Generic.IDictionary<_, _>) lbl = function
  | Some(((Indexed n) as ref)::_) when reverse.ContainsKey(ref) -> [ h?strong [] [ text (lbl + ": ") ]; text (reverse.[ref]) ]
  | Some(((Named n) as ref)::_) when reverse.ContainsKey(ref) -> [ h?strong [] [ text (lbl + ": ") ]; text (sprintf "%s (%s)" reverse.[ref] n) ]
  | Some(Indexed n::_) -> [ h?strong [] [ text (lbl + ": ") ]; text (sprintf "unnamed [%d]" n) ]
  | Some(Named n::_) -> [ h?strong [] [ text (lbl + ": ") ]; text n ]
  | _ -> [ h?strong [] [ text lbl ] ]

let (|GetValue|_|) state ref = getValue state ref

let formatExpression source (reverse:System.Collections.Generic.IDictionary<_, _>) expr = 
  let fref ref = h?em [] [ text (reverse.[ref]) ]
  let fsep refs = 
    [ for i, r in Seq.indexed refs do
        if i <> 0 then yield text ", "
        yield fref r ]
  [ match expr with
    | External s -> yield h?strong [] [ text s ] 
    | Value(OperationValue(Some(inps, out), _), _) ->
        yield text "("
        yield! fsep inps
        yield text ") "
        yield h?i ["class" => "fas fa-long-arrow-alt-right"] []
        yield text " "
        yield fref out
    | Value(OperationValue _, _) -> yield text "function"
    | Value(PrimitiveValue v, PrimitiveType "string") -> yield text (sprintf "\"%s\"" (string v))
    | Value(PrimitiveValue v, _) -> yield text (string v)
    | Value(v, _) -> yield text (string v)
    | Member(ref, s) -> 
        yield fref ref
        yield text "."
        yield h?strong [] [ text s ]
    | Invocation(inst, args) -> 
        match find inst source with 
        | Member(ref, s) ->
          yield fref ref
          yield text "."
          yield h?strong [] [ text s ]
          yield h?strong [] [ text "(" ]
          yield! fsep args
          yield h?strong [] [ text ")" ]
        | _ ->
          yield fref inst
          yield h?strong [] [ text "(" ]
          yield! fsep args
          yield h?strong [] [ text ")" ] ]

let renderHighlightSection trigger state =
    h?div [ "class" => "section section-highlighted" ] [
      let msg = 
        match state.HighlightedPath with
        | Some (((GetValue state v) as ref)::_) ->
            fst (getPreview ref trigger v (typeCheck state.Code ref) )
        | Some _ ->
            "Double click on a block to evaluate it."
        | _ -> 
            "Move mouse over a block to get quick info."
      yield h?div [ "class" => "header" ] [ 
        h.anim "phh" (hash state.HighlightedPath) <| h?span [] 
          (printPathReference (dict []) "quick info" state.HighlightedPath)
      ]
      yield h?div [ "class" => "body" ] [ 
        h.anim "phb" (hash msg) <| h?div [] [
          h?span [ "class" => "text" ] [  text msg ] ]
      ]
    ]

let renderSelectedSection label reverse trigger state =
    h?div [ "class" => "section section-selected" ] [
      let msg, body = 
        match state.SelectedPath with
        | Some (((GetValue state v) as ref)::_) ->
            getPreview ref trigger v (typeCheck state.Code ref) 
        | Some (ref::_) ->
            "", Some <| h?div [] [ 
              h?span ["class" => "text"] [text "Double click on a block to evaluate it." ]
              h?button [
                "class" => "evaluate"
                "click" =!> fun _ e -> e.cancelBubble <- true; trigger(justInteract(Evaluate ref)) 
              ] [ text "evaluate" ]
            ]
        | _ -> 
            "Click on a code block to select it.", None
      let body = defaultArg body (h?span [ "class" => "text" ] [ text msg ])
      yield h?div [ "class" => "header" ] [ 
        h.anim "psh" (hash state.SelectedPath) <| h?span [] 
          (printPathReference reverse label state.SelectedPath)
      ]
      yield h?div [ "class" => "body" ] [ 
        h.anim "psb" (hash msg) <| h?div [] [
          h?span [ "class" => "text" ] [ body ] ]
      ]
    ]

let renderCreateSection (reverse:System.Collections.Generic.IDictionary<_, _>) trigger state =
    let ctx = { Trigger = trigger; State = state; Code = state.Code.Source; Variables = Map.empty }
    h?div [ "class" => "section section-create" ] [
      yield h?div [ "class" => "header" ] [ 
        h.anim "pch" (hash state.SelectedPath) <| h?span [] 
          ( match state.CurrentCompletions with
            | Some(Indexed -1, _) -> [ h?strong [] [ text ("completions: ") ]; text "add code" ]
            | _ -> printPathReference reverse "completions" state.SelectedPath )
      ]
      yield h?div [ "class" => "body" ] [ 
        match state.SelectedPath with
        | Some(ref::_) ->
            yield h?span [ "class" => "source item" ] 
              ((h?span [] [text "Source: "])::(formatExpression state.Code.Source reverse (find ref state.Code.Source)))
            yield h?hr [] []
        | _ -> ()
        match state.CurrentCompletions, state.CurrentValue with
        | Some(Indexed -1, _), Some v ->  
            yield renderCompletions ctx [
              h?span [] [ text "enter new value" ]
              h?input [
                "input" =!> fun e _ -> trigger(UpdateAddValue(Some(unbox<Browser.HTMLInputElement>(e).value)))
                "click" =!> fun _ e -> e.cancelBubble <- true
                "value" => v
                "keydown" =!> fun _ k ->
                  match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
                  | 13 -> trigger(FinishAddValue)
                  | 27 -> trigger(UpdateAddValue None)
                  | _ -> () ] []
              ]

        | Some(Indexed -1, _), None ->
            yield renderCompletions ctx [
              yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; trigger(UpdateAddValue (Some "")) ] [ text "add value" ]
              yield h?hr [] []
              for (KeyValue(k, _)) in ctx.State.Code.External ->
                h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(DefineExternal k)) ] [ text k ]
            ]

        | Some(k, compl), _ ->
            yield renderCompletions ctx [
              match ctx.State.CurrentName with
              | Some(ref, n) ->
                  yield h?span [] [ text "enter variable name" ]
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
              match ctx.State.CurrentFunction with
              | Some ref ->
                  for inp in getInputs ctx.State.Code ref ->
                    h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(Abstract([inp], k)))] [ text ("taking " + formatReferencedExpr ctx inp) ]
              | _ ->
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCurrentFunction(Some(k))) ] [ text "Create function" ]
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateName(Some(k, ""))) ] [ text "Name cell" ]
                if not (List.isEmpty compl) then
                  yield h?hr [] []
                  let formatCompl = function
                    | NamedCompletion n -> [ h?em[] [ text "Select " ]; text n ]
                    | ParameterCompletion pars -> 
                        [ yield h?em[] [ text "Apply "]
                          for n, r in pars do
                            yield h?strong [] [ text n ]
                            yield text " = "
                            yield text (formatReferencedExpr ctx r) ] 
                  for n, c in compl -> h?a ["href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(Complete c)) ] (formatCompl n)
            ]
        | _ -> 
          yield h?span [ "class" => "item" ] [ text "Click on a code block to see completions." ]        
      ]
    ]

let renderCode trigger (state:Model) = 
  let code = state.Code.Source
  let allRefs = code |> Seq.collect (snd >> collectReferences code) |> set
  let ctx = { Code = state.Code.Source; Trigger = trigger; Variables = Map.empty; State = state }
  h?div
    [ "class" => "code"
      "mousemove" =!> fun _ e ->
        e.cancelBubble <- true
        if state.HighlightedPath <> None then trigger (Highlight(None))
      "mouseleave" =!> fun _ e ->
        e.cancelBubble <- true
        if state.HighlightedPath <> None then trigger (Highlight(None))
    ] [
      for ref, _ in code ->
        h?div ["class" => "indent"] [
          match ref, allRefs.Contains ref with
          | Named n, _ ->
              yield h?span [ "class" => "let" ] [ h?strong [] [ text "let" ]; text (" " + n + " = ") ]
              //yield renderReferencedExpression ctx ref
              yield h?div [ "class" => "indent" ] (renderExpression ctx ([ref], ref) (find ref ctx.Code))
              //yield h?span [ "class" => "indent" ] (renderReferencedExpression ctx ([ref], ref))

          | Indexed n, false ->
              yield h?span [ "class" => "let" ] [ h?strong [] [ text (sprintf "cell[%d]" n) ] ]
              yield h?div [ "class" => "indent" ] (renderReferencedExpression ctx ([ref], ref))
          | _ -> ()
        ]
      yield h?div [ "class" => "indent" ] [
        yield h?span [ "class" => "let" ] [ text "cell" ]
        yield h?div [ "style" => "display:inline-block" ] [
          yield h?button [
            "class" => "plus"
            "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCompletions(Some (Indexed -1)))
          ] [ text "+" ]
          match state.CurrentCompletions, state.CurrentValue with
          | Some(Indexed -1, _), Some v ->
              yield renderCompletions ctx [
                h?span [] [ text "enter new value" ]
                h?input [
                  "input" =!> fun e _ -> trigger(UpdateAddValue(Some(unbox<Browser.HTMLInputElement>(e).value)))
                  "click" =!> fun _ e -> e.cancelBubble <- true
                  "value" => v
                  "keydown" =!> fun _ k ->
                    match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
                    | 13 -> trigger(FinishAddValue)
                    | 27 -> trigger(UpdateAddValue None)
                    | _ -> () ] []
                ]
          | Some(Indexed -1, _), None ->
              yield renderCompletions ctx [
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; trigger(UpdateAddValue (Some "")) ] [ text "add value" ]
                yield h?hr [] []
                for (KeyValue(k, _)) in ctx.State.Code.External ->
                  h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(justInteract(DefineExternal k)) ] [ text k ]
              ]
          | _ -> ()
        ]
      ]
    ]

let createSheet (state:Model) =
  let groups = groupSource state.Code.Source 
  let cols = groups.Length + 1 |> max 10
  let rows = groups |> Array.map Array.length |> Array.fold max 0 |> max 15
  let cells = 
    Array.init cols (fun i ->
      if i < groups.Length then 
        Array.init rows (fun r -> if groups.[i].Length > r then Some groups.[i].[r] else None) 
      else Array.create rows None )
  let reverseLookup =
    [ for col, g in Seq.zip ['A' .. 'Z'] groups do
      for row, (ref, _) in Seq.indexed g do
      yield ref, sprintf "%c%d" col (row+1) ] |> dict    
  groups, cols, rows, cells, reverseLookup

let renderSheet (groups:_[], cols, rows, cells:_[][], reverseLookup) trigger (state:Model) =
  h?div ["class" => "sheet-wrapper"] [ h?table ["class" => "sheet"] [ 
    yield h?thead [] [ h?tr [] [ 
      yield h?th [] []
      for col in Seq.take cols ['A' .. 'Z'] -> h?th [] [ h?div [] [ text (string col) ] ]
    ] ]
    for row in 0 .. rows - 1 -> h?tr [] [
      yield h?th [] [ h?div [] [ text (string (row + 1)) ] ]
      for col in 0 .. cols - 1 -> h?td [] [
        match cells.[col].[row] with
        | None when col = groups.Length && row = 0 ->
            yield h?div [ "class" => "tool" ] [ h?button [
              "class" => "plus"
              "click" =!> fun _ e -> e.cancelBubble <- true; trigger(UpdateCompletions(Some (Indexed -1)))
            ] [ text "add code" ] ]
        | None -> ()
        | Some (ref, expr) ->
            yield h?div [
              "class" =>
                if Some [ref] = state.SelectedPath then "expr selected"
                elif Some [ref] = state.HighlightedPath then "expr highlighted"
                else "expr"
              "dblclick" =!> fun _ e ->
                e.cancelBubble <- true
                Browser.window.getSelection().removeAllRanges()
                trigger(justInteract(Evaluate ref)) 
              "click" =!> fun _ e ->
                e.cancelBubble <- true
                if state.SelectedPath <> Some [ref] then 
                  trigger (UpdateCurrentFunction None)
                  trigger (Select(Some [ref]))
                match state.CurrentCompletions with 
                | Some(r, _) when r = ref -> () 
                | _ -> trigger(UpdateCompletions(Some ref))
              "mousemove" =!> fun _ e ->
                e.cancelBubble <- true
                if state.HighlightedPath <> Some [ref] then trigger (Highlight(Some [ref]))
            ] (formatExpression state.Code.Source reverseLookup expr)
      ]
    ]
  ] ]

(*    for g in groups -> rows "chain" [
      for ref, v in g -> 
        h?div [
          yield "class" =>
            if Some [ref] = state.SelectedPath then "expr selected"
            elif Some [ref] = state.HighlightedPath then "expr highlighted"
            else "expr"
          yield "dblclick" =!> fun _ e ->
            e.cancelBubble <- true
            Browser.window.getSelection().removeAllRanges()
            trigger(Interact(Evaluate ref)) 
          yield "click" =!> fun _ e ->
            e.cancelBubble <- true
            if state.SelectedPath <> Some [ref] then trigger (Select(Some [ref]))
          yield "mousemove" =!> fun _ e ->
            e.cancelBubble <- true
            if state.HighlightedPath <> Some [ref] then trigger (Highlight(Some [ref]))
        ] [
          //yield h?strong [] [ text (formatReference ref) ]
          //yield h?br [] []
          if Some [ref] = state.HighlightedPath || Some [ref] = state.SelectedPath then 
            match getValue state ref with
            | Some(v) ->
                let s, html = getPreview trigger v (typeCheck state.Code ref)
                yield h?span [] [ text s ]
            | None ->
                yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(Interact(Evaluate ref)) ] [ text "evaluate" ]
          else
            yield text (formatExpression v)
            ]


          (*
        match v, state.CurrentReplace with
        | Value(_, PrimitiveType t), Some(ref, v) when ref = k ->
            yield h?input [
              "input" =!> fun e _ -> trigger(UpdateReplace(Some(ref, unbox<Browser.HTMLInputElement>(e).value)))
              "value" => v
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

        match state.CurrentCompletions with
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
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateCompletions(Some k)) ] [ text "completions" ]
            yield h?br [] []
            *)
      ]
    yield h?div [] [
      match state.CurrentValue with
      | None ->
          yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(UpdateAddValue (Some "")) ] [ text "Add value" ]
      | Some v ->
          yield text "Add value"
          yield h?br [] []
          yield h?input [
            "input" =!> fun e _ -> trigger(UpdateAddValue(Some(unbox<Browser.HTMLInputElement>(e).value)))
            "value" => v
            "keydown" =!> fun _ k ->
              match int (unbox<Browser.KeyboardEvent>(k).keyCode) with
              | 13 -> trigger(FinishAddValue)
              | 27 -> trigger(UpdateAddValue None)
              | _ -> () ] []
    ]
  ] ]
  *)
module Serializer =
  let createObj = Fable.Core.JsInterop.createObj
  let (=>) k v = k, box v
  let (?) = JsInterop.(?)

  let serializeRef = function
    | Named n -> box n
    | Indexed i -> box i

  let serializeInteraction = function
    | Complete(Dot(ref, mem)) -> createObj [ "kind" => "dot"; "reference" => serializeRef ref; "member" => mem ]
    | Complete(Apply(op, arg, ref)) -> createObj [ "kind" => "apply"; "operation" => serializeRef op; "arguments" => [| [| box arg; serializeRef ref |] |] ]
    | Name(ref, name) -> createObj [ "kind" => "name"; "reference" => serializeRef ref; "name" => name ]
    | Evaluate(ref) -> createObj [ "kind" => "evaluate"; "reference" => serializeRef ref ]
    | Abstract(args, res) -> createObj [ "kind" => "abstract"; "arguments" => [| for a in args -> serializeRef a |]; "output" => serializeRef res ]
    | DefineValue(PrimitiveValue v, PrimitiveType typ) -> createObj [ "kind" => "value"; "value" => v; "type" => typ ]
    | ReplaceValue(ref, PrimitiveValue v, PrimitiveType typ) -> createObj [ "kind" => "replace"; "reference" => serializeRef ref; "value" => v; "type" => typ ]
    | DefineExternal(s) -> createObj [ "kind" => "extern"; "name" => s ]
    | ReplaceValue _
    | DefineValue _ -> failwith "Cannot serialize value"

  let serializeEvent = function
    | Caption(n, s) -> createObj [ "kind" => "caption"; "number" => n; "text" => s ]
    | Interact(i, _) -> createObj [ "kind" => "interact"; "interaction" => serializeInteraction i ]
    | Select(None) -> createObj [ "kind" => "noselect" ]
    | Highlight(None) -> createObj [ "kind" => "nohighlight" ]
    | SelectMenu(None) -> createObj [ "kind" => "nomenu" ]
    | Select(Some refs) -> createObj [ "kind" => "select"; "path" => Array.map serializeRef (Array.ofSeq refs) ]
    | Highlight(Some refs) -> createObj [ "kind" => "highlight"; "path" => Array.map serializeRef (Array.ofSeq refs) ]
    | SelectMenu(Some n) -> createObj [ "kind" => "menu"; "selected" => n ]
    | Backward -> createObj [ "kind" => "backward" ]
    | Forward -> createObj [ "kind" => "forward" ]
    //| Refresh -> createObj [ "kind" => "refresh" ]
    | UpdateCompletions None -> createObj [ "kind" => "nocompletions" ]
    | UpdateCurrentFunction None -> createObj [ "kind" => "nofunction" ]
    | FinishReplace -> createObj [ "kind" => "finishreplace" ]
    | FinishAddValue -> createObj [ "kind" => "finishvalue" ]
    | FinishNaming -> createObj [ "kind" => "finishnaming" ]
    | UpdateReplace None -> createObj [ "kind" => "noreplace" ]
    | UpdateAddValue None -> createObj [ "kind" => "novalue" ]
    | UpdateName None -> createObj [ "kind" => "noname" ]
    | UpdateCompletions(Some ref) -> createObj [ "kind" => "completions"; "reference" => serializeRef ref ]
    | UpdateCurrentFunction(Some ref) -> createObj [ "kind" => "function"; "reference" => serializeRef ref ]
    | UpdateReplace(Some (ref, r)) -> createObj [ "kind" => "repalce"; "reference" => serializeRef ref; "value" => r ]
    | UpdateAddValue(Some s) -> createObj [ "kind" => "value"; "value" => s ]
    | UpdateName(Some (ref, s)) -> createObj [ "kind" => "name"; "reference" => serializeRef ref; "name" => s ]

  let deserializeRef (o:obj) = match o with :? int as i -> Indexed i | :? string as s -> Named s | _ -> failwith "deserializeRef"

  let deserializeInteraction obj =
    match obj?kind with
    | "dot" -> Complete(Dot(deserializeRef obj?reference, obj?``member``))
    | "apply" ->
        let args = (obj?arguments : obj[][]).[0]
        Complete(Apply(deserializeRef obj?operation, unbox args.[0], deserializeRef args.[1] ))
    | "name" -> Name(deserializeRef obj?reference, obj?name)
    | "evaluate" -> Evaluate(deserializeRef obj?reference)
    | "abstract" -> Abstract(List.ofArray(Array.map deserializeRef obj?arguments), deserializeRef obj?output)
    | "value" -> DefineValue(PrimitiveValue obj?value, PrimitiveType obj?``type``)
    | "extern" -> DefineExternal(obj?name)
    | "replace" -> ReplaceValue(deserializeRef obj?reference, PrimitiveValue(obj?value), PrimitiveType(obj?``type``))
    | k -> failwithf "deserialize: Unexpected interaction kind: %s" k



  let deserializeEvent obj =
    match obj?kind with
    | "caption" -> Caption(obj?number, obj?text)
    | "noselect" -> Select(None)
    | "nohighlight" -> Highlight(None)
    | "nomenu" -> SelectMenu(None)
    | "select" -> Select(Some(List.ofArray (Array.map deserializeRef obj?path)))
    | "highlight" -> Highlight(Some(List.ofArray (Array.map deserializeRef obj?path)))
    | "menu" -> SelectMenu(Some obj?selected)
    | "interact" -> Interact (deserializeInteraction obj?interaction, ignore)
    | "backward" -> Backward
    | "forward" -> Forward
    //| "refresh" -> Refresh
    | "nocompletions" -> UpdateCompletions None
    | "nofunction" -> UpdateCurrentFunction None
    | "finishreplace" -> FinishReplace
    | "finishvalue" -> FinishAddValue
    | "finishnaming" -> FinishNaming
    | "noreplace" -> UpdateReplace None
    | "novalue" -> UpdateAddValue None
    | "noname" -> UpdateName None
    | "completions" -> UpdateCompletions(Some (deserializeRef obj?reference))
    | "function" -> UpdateCurrentFunction(Some (deserializeRef obj?reference))
    | "value" -> UpdateAddValue(Some obj?value)
    | "replace" -> UpdateReplace(Some (deserializeRef obj?reference, obj?value))
    | "name" -> UpdateName(Some (deserializeRef obj?reference, obj?name))
    | k -> failwithf "deserialize: Unexpected event kind: %s" k

  let deserializeEvents json =
    let objs = Fable.Import.JS.JSON.parse(json) :?> obj[]
    [| for evt in objs -> deserializeEvent evt |]

let renderSource (events:seq<Event>) (state:Model) =
  h?textarea [ "class" => "debug" ] [
    yield text "[\n"
    for e in events -> text ("  " + Fable.Import.JS.JSON.stringify(Serializer.serializeEvent e) + ",\n")
    yield text "]"
  ]

let viewHeader unclip id trigger state title = 
  let makeIcon title fa enabled f = 
    h?a  
      [ "href" => "javascript:;"; "title" => title
        "click" =!> fun _ _ -> if enabled then f() ] 
      [ h?i [ "class" => "fa fa-" + fa + (if enabled then "" else " disabled") ] [] ]

  h?div [ "class" => "row" ] [
    h?div [ "class" => "col-sm-12 demo-top" ] [
      h?div [ "class" => "tools" ] [
        makeIcon "Turn auto-play on again and lose all edits." "paperclip" state.Modified unclip
        makeIcon "Jump to the start of the interactive demo." "angle-double-left" true (fun () ->
          let s = Browser.document.getElementById(id)
          Browser.window.scrollTo(0., s.offsetTop) )
        makeIcon "Undo the last interaction with the system." "angle-left" (not (List.isEmpty state.Program)) (fun () -> trigger(Backward))        
        makeIcon "Redo a previously undone interaction." "angle-right" (not (List.isEmpty state.Forward)) (fun () -> trigger(Forward))        
        makeIcon "Jump to the end of the interactive demo." "angle-double-right" true (fun () ->
          let s = Browser.document.getElementById(id)
          Browser.window.scrollTo(0., s.offsetTop + s.offsetHeight - Browser.window.innerHeight) )
      ]
      h?h2 [] [ h?a [ "name" => id ] [ h?strong [] [ text "Demo: " ]; text title ] ]
    ]
  ]

let viewCode unclip id title events trigger state = 
  h?div [] [
    viewHeader unclip id trigger state title
    h?div [ "class" => "row" ] [
      h?div [ "class" => "col-sm-12 interactive" ] [
        h?table [
            "class" => "split"
            "click" =!> fun _ e -> e.cancelBubble <- true; trigger (Select(None))
          ] [ h?tr [] [ 
            h?td ["class" => "code"] [ renderCode trigger state ]
            h?td ["class" => "preview"] [ 
              h?div [ "class" => "preview"; "click" =!> fun _ e -> e.cancelBubble <- true ] [
                renderHighlightSection trigger state
                renderSelectedSection "selected" (dict []) trigger state ]
           ]
          ] ]
      ] 
      //h?div [ "class" => "col-sm-4" ] [ renderSource events state ]
    ] 
    h?div [ "class" => "row" ] [
      h?div [ "class" => "col-sm-7 large-caption" ] [
        match state.Caption with 
        | Some (n, s) ->
            yield h?span [ "class" => "num" ] [ h?span [] [ text (string n) ] ]  
            for p in s.Split('\n') -> h?p [] [ text p ]
        | _ -> ()
      ] 
    ]
  ]

let viewSheet unclip id title events trigger state = 
  h?div [] [
    viewHeader unclip id trigger state title
    h?div [ "class" => "row" ] [
      h?div [ "class" => "col-sm-12 interactive" ] [
        h?table [
            "class" => "split"
            "click" =!> fun _ e -> e.cancelBubble <- true; trigger (Select(None))
          ] [ h?tr [] [ 
            let (_, _, _, _, reverse) as sheet = createSheet state
            yield h?td ["class" => "sheet"] [ renderSheet sheet trigger state ]
            yield h?td ["class" => "preview"] [ 
              h?div [ "class" => "preview"; "click" =!> fun _ e -> e.cancelBubble <- true ] [
                renderCreateSection reverse trigger state
                renderSelectedSection "preview" reverse trigger state ]
              ]
          ] ]
      ] 
      //h?div [ "class" => "col-sm-4" ] [ renderSource events state ]
    ] 
    h?div [ "class" => "row" ] [
      h?div [ "class" => "col-sm-7 large-caption" ] [
        match state.Caption with 
        | Some (n, s) ->
            yield h?span [ "class" => "num" ] [ h?span [] [ text (string n) ] ]  
            for p in s.Split('\n') -> h?p [] [ text p ]
        | _ -> ()
      ] 
    ]
  ]


// ------------------------------------------------------------------------------------------------
// Demo types
// ------------------------------------------------------------------------------------------------

let download url =
  Async.FromContinuations (fun (cont, _, _) ->
    let data = Fetch.fetch url []
    ignore(data.``then``(fun v ->
      ignore (v.text().``then``(fun v ->
        let data = v.Split('\n') |> Array.filter (fun row -> row.Trim() <> "") |> Array.map (fun row -> row.Split(','))
        cont data )))))

type RowObjectValue =
  inherit ObjectValue
  abstract Headers : (string * Type)[]
  abstract Data : string[]

type FrameObjectValue =
  inherit ObjectValue
  abstract Headers : (string * Type)[]

let rec rowType columns =
  { new ObjectType with
    member x.Refine v =
      match v with
      | ObjectValue(ov) -> rowType (ov :?> RowObjectValue).Headers
      | _ -> failwith "rowType: Expected RowObjectValue"
    member x.Members =
      ("lookup",  OperationType(["name", PrimitiveType "string"], PrimitiveType "string")) :: List.ofSeq columns }

let rowValue headers values =
  let data = Array.zip headers values
  let parse v = match System.Int32.TryParse(v) with true, r -> PrimitiveValue r | _ -> PrimitiveValue v
  let row =
    { new RowObjectValue with
      member x.Hash = hash data
      member x.Data = values
      member x.Headers = headers
      member x.Preview(_) = 
        sprintf "Block is a record with %d attributes." headers.Length,
        Some (renderTable [ [text "attribute"]; [text "value"] ] [ for (k, _), v in data -> [[text k]; [text v]] ])

      member x.Lookup m =
        if m = "lookup" then OperationValue(None, fun [PrimitiveValue m] -> async {
          return data |> Seq.pick (fun ((k, _), v) -> if k = unbox m then Some(PrimitiveValue v) else None) })
        else data |> Seq.pick (fun ((k, _), v) -> if k = m then Some(parse v) else None) }
  ObjectValue(row :> ObjectValue)

let sortByType keys resTyp =
  { new ObjectType with
      member x.Refine _ = x
      member x.Members =
        [ for k in keys do
            yield k + " ascending", resTyp
            yield k + " descending", resTyp ] } |> ObjectType

let filterByType headers resTyp =
  { new ObjectType with
      member x.Refine _ = x
      member x.Members =
        [ for k,t in headers do
            yield k + " equals", OperationType(["value", t], resTyp)
            yield k + " not equals", OperationType(["value", t], resTyp) ] } |> ObjectType

let framePreview ctx headers (rows:(string[] * Value)[]) = 
  let getRef ref = async {
      let! ref = ref
      match ref with Some ref -> return ref | _ -> return failwith "framePreview: Expected some reference" }

  let interactSortBy order k = Async.StartImmediate <| async {
    let! sortRef = ctx.Interact (Complete(Dot(ctx.Reference, "sort by"))) |> getRef
    let! finalRef = ctx.Interact (Complete(Dot(sortRef, k + " " + order))) |> getRef
    let! _ = ctx.Interact (Evaluate(finalRef)) 
    ctx.Select finalRef }

  let interactAt i = Async.StartImmediate <| async {
    let! atRef = ctx.Interact (Complete(Dot(ctx.Reference, "at"))) |> getRef
    let! valRef = ctx.Interact(DefineValue(PrimitiveValue(float i), PrimitiveType("number"))) |> getRef
    let! applyRef = ctx.Interact (Complete(Apply(atRef, "index", valRef))) |> getRef
    let! _ = ctx.Interact (Evaluate(applyRef)) 
    ctx.Select applyRef }

  let interactEquals neq isNumeric k v = Async.StartImmediate <| async {
    let! filterRef = ctx.Interact (Complete(Dot(ctx.Reference, "filter by"))) |> getRef
    let! opRef = ctx.Interact (Complete(Dot(filterRef, k + (if neq then " not equals" else " equals") ))) |> getRef
    let! valRef = 
      ( if isNumeric then ctx.Interact(DefineValue(PrimitiveValue(float v), PrimitiveType("number"))) 
        else ctx.Interact(DefineValue(PrimitiveValue(string v), PrimitiveType("string"))) ) |> getRef
    let! finalRef = ctx.Interact (Complete(Apply(opRef, "value", valRef))) |> getRef
    let! _ = ctx.Interact (Evaluate(finalRef)) 
    ctx.Select finalRef }

  let makeSortLink k cls order = 
    h?i [ 
      "class" => "fa fa-" + cls
      "click" =!> fun e _ -> interactSortBy order k ] []

  let theaders = 
    [ yield [ text "#" ]
      for k, _ in headers -> [
        text k
        makeSortLink k "sort-up" "descending"
        makeSortLink k "sort-down" "ascending" ] ]

  let tbody =          
    [ yield [ 
        yield [ h?i ["class" => "fa fa-filter"] [] ]
        for i, (k, t) in Seq.indexed headers -> [ h?select [
            "change" =!> fun e _ -> 
                let v = unbox<Browser.HTMLSelectElement>(e).value
                interactEquals (v.[0] = '!') (t = PrimitiveType "number") k (v.Substring(1))
            "mousedown" =!> fun e _ ->
              if e.children.length = 1. then
                for v in rows |> Seq.map (fun (r, _) -> r.[i]) |> Seq.distinct do
                  let o1 = Browser.document.createElement_option()
                  o1.value <- "=" + v
                  o1.innerText <- "equals " + v
                  let o2 = Browser.document.createElement_option()
                  o2.value <- "!" + v
                  o2.innerText <- "not equals " + v
                  e.appendChild(o1) |> ignore
                  e.appendChild(o2) |> ignore
          ] [
            h?option ["value" => ""]  [ text "all" ]
          ] ] ]
      for i, (a, _) in Seq.indexed (Seq.truncate 200 rows) -> [
        yield [ h?span [ "class" => "index"
                         "click" =!> fun _ _ -> interactAt i ] [ text (string i) ] ]
        for v in a -> [ text v ] ] ]

  sprintf "Block is a table with %d rows." rows.Length,
  Some (renderTable theaders tbody)

let frameValue (data:string[][]) =
  let inferType v = match System.Int32.TryParse(v) with true, _ -> PrimitiveType "number" | _ -> PrimitiveType "string"
  let headers = Array.map2 (fun h v -> h, inferType v) data.[0] data.[1]
  let rows = data.[1..] |> Array.map (fun a -> a, rowValue headers a)
  let rec v (rows:(string[] * Value)[]) =
    let fov =
      { new FrameObjectValue with
        member x.Headers = headers
        member x.Hash = hash [for _, (ObjectValue r) in rows -> r.Hash ]
        member x.Preview(ctx) = framePreview ctx headers rows
        member x.Lookup m =
          if m = "at" then OperationValue(None, function
            | [PrimitiveValue n] -> async.Return(snd rows.[unbox n])
            | _ -> failwith "frameValue: Invalid index in 'at'")

          elif m = "sum" then
            let headers, data =
             [| for colIndex, (colName, colTyp) in Seq.indexed headers do
                  if colTyp = PrimitiveType "number" then
                    let safefloat f = try float f with _ -> 0.0
                    yield (colName, colTyp), string (Seq.sum [ for r, _ in rows -> safefloat (r.[colIndex]) ]) |] |> Array.unzip
            rowValue headers data

          elif m = "filter" then OperationValue(None, function
            | [OperationValue(_, f)] -> async {
                let resRows = ResizeArray<_>()
                for k, r in rows do
                  let! add = f [r]
                  match add with
                  | PrimitiveValue(b) when unbox b = true -> resRows.Add(k, r)
                  | _ -> ()
                return v (resRows.ToArray()) }
            | _ -> failwith "frameValue.filter: Invalid predicate")

          elif m = "sort by" then
            let fov =
              { new FrameObjectValue with
                member y.Headers = x.Headers
                member y.Hash = x.Hash
                member y.Preview(c) = x.Preview(c)
                member x.Lookup m =
                  let asc = m.EndsWith(" ascending")
                  let m = m.Replace(" ascending", "").Replace(" descending", "")
                  let index = headers |> Array.findIndex (fun (h, _) -> h = m)
                  let isNumeric = snd headers.[index] = PrimitiveType "number"
                  let sort f = 
                    if isNumeric then (if asc then Array.sortBy (f >> float) else Array.sortByDescending (f >> float))
                    else (if asc then Array.sortBy f else Array.sortByDescending f)
                  rows |> sort (fun (data, _) -> data.[index]) |> v }
            ObjectValue(fov :> ObjectValue)

          elif m = "filter by" then
            let fov =
              { new FrameObjectValue with
                member y.Headers = x.Headers
                member y.Hash = x.Hash
                member y.Preview(c) = x.Preview(c)
                member x.Lookup m =
                  let neq = m.EndsWith(" not equals")
                  let m = m.Replace(" not equals", "").Replace(" equals", "")
                  let index = headers |> Array.findIndex (fun (h, _) -> h = m)
                  OperationValue(None, fun [PrimitiveValue v1] -> async {
                    let isNumeric = snd headers.[index] = PrimitiveType "number"
                    let check (v2:string) = 
                      let eq = if isNumeric then unbox<float> v1 = unbox<float> v2 else unbox<string> v1 = unbox<string> v2
                      if neq then not eq else eq
                    return rows |> Array.filter (fun (data, _) -> check data.[index]) |> v }
                  ) }
            ObjectValue(fov :> ObjectValue)

          else failwith "frameValue: Member not found" }
    ObjectValue(fov :> ObjectValue)
  v rows

let rec frameType columns =
  let rt = ObjectType(rowType columns)
  { new ObjectType with
      member x.Refine v =
        match v with
        | ObjectValue(ov) -> frameType (ov :?> FrameObjectValue).Headers
        | _ -> failwith "frameType: Expected FrameObjectValue"
      member x.Members =
        [ yield "at", OperationType(["index", PrimitiveType "number"], rt)
          yield "sort by", sortByType (Array.map fst columns) (ObjectType(frameType columns))
          yield "sum", ObjectType(rowType [||])
          yield "filter", OperationType(["predicate", OperationType(["row", rt], PrimitiveType "bool")], ObjectType(frameType columns))
          yield "filter by", filterByType columns (ObjectType(frameType columns))
        ] }

let createDataFrame file = async {
  let! data = download file
  return frameValue data, frameType [||] }

let data files = async {
  let frames = System.Collections.Generic.Dictionary<_, _>()
  for k, file in files do
    let! frame = createDataFrame file
    frames.Add(k, frame)
  let value =
    { new ObjectValue with
      member x.Hash = hash files
      member x.Preview(_) =
        "data source",
        Some <| h?ul [] [
          for k, file in files -> h?li [] [ h?strong [] [ text k ]; text (sprintf " (%s)" file) ]
        ]
      member x.Lookup m =
        if m = "load" then OperationValue(None, fun [PrimitiveValue url] -> async {
          let! data = download (url :?> string)
          return frameValue data })
        else
          fst frames.[m] } |> ObjectValue
  let typ =
    { new ObjectType with
      member x.Refine _ = x
      member x.Members =
        [ yield "load", OperationType(["url", PrimitiveType "string"], ObjectType(frameType [||]))
          for k, _ in files -> k, ObjectType(snd frames.[k]) ] } |> ObjectType
  return value, typ }

let rec barChartType =
  { new ObjectType with
    member x.Refine _ = x
    member x.Members = ["add series", OperationType(["data", ObjectType(rowType [||])], barChartType) ] } |> ObjectType

let rec barChartValue (rows:RowObjectValue list) =
  { new ObjectValue with
    member x.Hash = 0
    member x.Preview(_) =
      let colors = Seq.initInfinite (fun _ ->
        [ "#996380" ]) |> Seq.concat

      let headers = (List.head rows).Headers |> Array.map fst
      let headers = List.tail rows |> List.fold (fun headers row ->
        headers |> Array.filter (fun h -> row.Headers |> Array.exists (fun (h2, _) -> h = h2))) headers
      let lookups = rows |> List.map (fun row -> dict (Seq.zip (Array.map fst row.Headers) row.Data)  )

      let viz =
        Shape.Layered [
          for h in headers do
          for clr, (n, v) in Seq.zip colors (Seq.indexed lookups) do
          let n, v = (if rows.Length = 1 then h else sprintf "%s (%d)" h n), float v.[h]
          let bar n = Shape.Padding((2., 0., 2., 1.), Derived.Bar(CO v, CA n))
          yield Shape.Style((fun s -> { s with Fill = Solid(1.0, HTML clr) }), bar n)
        ]

      let secElem = Browser.document.getElementsByClassName("section-highlighted").[0]
      let width = (unbox<Browser.HTMLElement> secElem).offsetWidth - 25.0
      let height = Browser.window.innerHeight - 400.0

      let viz = Shape.Axes(false, false, true, true, viz)
      "chart", 
      Some (Compost.createSvg false false (width, height) viz)
    member x.Lookup n =
      if n = "add series" then OperationValue(None, fun [ObjectValue row] -> async {
        return barChartValue [ yield! rows; yield row :?> RowObjectValue] })
      else
        failwithf "chart: member %s does not exist" n } |> ObjectValue

let chart =
  { new ObjectValue with
    member x.Hash = 0
    member x.Preview(_) = "chart", None
    member x.Lookup m =
      if m = "bar" then OperationValue(None, fun [ObjectValue row] -> async {
        return barChartValue [row :?> RowObjectValue] })
      else
        failwithf "chart: member %s does not exist" m } |> ObjectValue,
  { new ObjectType with
    member x.Refine _ = x
    member x.Members = ["bar", OperationType(["data", ObjectType(rowType [||])], barChartType) ] } |> ObjectType


let createScrolly (unclip:IEvent<_>) id stepHeight stepCount trigger =
  let stepHeight, stepCount = float stepHeight, float stepCount
  let s = Browser.document.getElementById(id)
  let sb = Browser.document.getElementById(id + "-body")
  
  let mutable lastStep = -1
  let mutable section = 0 // 0, 1 or 2

  let resize () =
    let hgt = Browser.window.innerHeight + stepHeight * stepCount
    s.style.height <- (string hgt) + "px"

  let trigger n = 
    if lastStep <> n then 
      lastStep <- n
      Browser.window.setTimeout((fun () -> trigger n), 50) |> ignore

  let update () = 
    if Browser.window.scrollY < s.offsetTop then
      if section <> 0 then
        section <- 0
        sb.style.position <- "relative"
        sb.style.top <- "0px"
      trigger 0
    elif Browser.window.scrollY > s.offsetTop + (stepHeight * stepCount) then
      if section <> 2 then  
        section <- 2
        sb.style.position <- "relative"
        sb.style.top <- string (stepHeight * stepCount) + "px"
      trigger (int stepCount - 1)
    else
      if section <> 1 then
        section <- 1
        sb.style.position <- "fixed"
        sb.style.top <- "0px"
        sb.style.width <- "100vw"
        sb.style.height <- (string Browser.window.innerHeight) + "px"
      let step = int ((Browser.window.scrollY - s.offsetTop) / stepHeight)
      trigger (min (int stepCount - 1) (max 0 step))

  update()
  resize() 
  
  unclip.Add(fun () -> lastStep <- -1; section <- -1; update ())

  let oldresize = Browser.window.onresize
  Browser.window.onresize <- fun e ->
    if unbox oldresize <> null then oldresize(e)
    resize ()

  let oldscroll = Browser.window.onscroll
  Browser.window.onscroll <- fun e ->
    if unbox oldscroll <> null then oldscroll(e)
    update ()
    
let readCaptions id = 
  let caps = Browser.document.getElementById(id).innerText.Trim(' ', '*', '/')
  let caps = caps.Split([|'\r';'\n'|], System.StringSplitOptions.RemoveEmptyEntries)
  [| for i, cap in Seq.indexed caps -> 
       let r = cap.Split(':')
       int r.[0], sprintf "<span class='num'><span>%d</span></span><p>%s</p>" (i+1) (r.[1].Trim()) |]

let createSlideshow ppf prefix images =
  let images = images |> Array.map (fun f -> Browser.Image.Create(src = f))
  let imga = Browser.document.getElementById(prefix + "-frame-a")
  let imgb = Browser.document.getElementById(prefix + "-frame-b")
  let mutable imgs = unbox<Browser.HTMLImageElement> imga, unbox<Browser.HTMLImageElement> imgb
  let captions = readCaptions (prefix + "-captions")
  createScrolly (new Event<_>()).Publish prefix ppf images.Length (fun i ->
    let iprev, inext = imgs
    inext.src <- images.[i].src
    iprev.className <- "frame-out"
    inext.className <- "frame-in"
    imgs <- inext, iprev
    let cap = Browser.document.getElementById(prefix + "-caption")
    cap.innerHTML <- captions |> Seq.takeWhile (fun (ci, _) -> ci <= i) |> Seq.last |> snd  
  )

module Showdown = 
  let (?) = JsInterop.(?)
  type IConverter = 
    abstract makeHtml : string -> string
  [<Import("Converter", "showdown")>]
  let converterProto : IConverter = jsNative
  let converter : IConverter = JsInterop.createNew converterProto () |> unbox

let stripSpaces (md:string) =
  let lines = md.Split([| '\r'; '\n' |])
  let spaces = lines |> Seq.filter (System.String.IsNullOrWhiteSpace >> not) |> Seq.map (fun line ->
    line.Length - line.TrimStart(' ').Length) |> Seq.min
  lines |> Seq.map (fun s -> if s.Length > spaces then s.Substring(spaces) else s) |> String.concat "\n"

let mdElements = Browser.document.getElementsByClassName("markdown")
let reg = System.Text.RegularExpressions.Regex("\$([^\$]*)\$")
for i in 0 .. int mdElements.length - 1 do
  let el = mdElements.[i]
  let html = Showdown.converter.makeHtml(stripSpaces(el.innerHTML.Replace("&gt;",">")))
  let html = reg.Replace(html, fun m -> "\(" + m.Value.Trim('$') + "\)")
  el.innerHTML <- html.Replace("--", "&ndash;")

let h2Elements = Browser.document.getElementsByTagName("h2")
for i in 0 .. int h2Elements.length - 1 do
  let el = h2Elements.[i] |> unbox<Browser.HTMLElement>
  let a = Browser.document.createElement_a()
  a.setAttribute("name", "s"+ el.innerText.[0].ToString())
  for _ in 0 .. int el.children.length - 1 do a.appendChild(el.removeChild(el.lastChild)) |> ignore
  el.appendChild(a) |> ignore

let h3Elements = Browser.document.getElementsByTagName("h3")
for i in 0 .. int h3Elements.length - 1 do
  let el = h3Elements.[i] |> unbox<Browser.HTMLElement>
  let a = Browser.document.createElement_a()
  a.setAttribute("name", "s"+ el.innerText.[0].ToString() + "_" + el.innerText.[2].ToString())
  for _ in 0 .. int el.children.length - 1 do a.appendChild(el.removeChild(el.lastChild)) |> ignore
  el.appendChild(a) |> ignore
  
let latexElements = Browser.document.getElementsByClassName("mathjax")
for i in 0 .. int latexElements.length - 1 do
  let el = latexElements.[i] |> unbox<Browser.HTMLElement>
  el.parentElement.outerHTML <- "<div class='mathjax'>\(" + el.innerText + "\)</div>"

let createEvalAgent update initial (events:_[]) = MailboxProcessor<_ * AsyncReplyChannel<_>>.Start(fun inbox -> async {
  let cache = System.Collections.Generic.Dictionary<_, _>()
  cache.[0] <- initial
  try
    while true do
      let! i, repl = inbox.Receive()
      let lastComputed = [i .. -1 .. 0] |> Seq.find (fun i -> cache.ContainsKey i)
      for i in lastComputed+1 .. i do
        //printfn "evaluating: %d, %s" i (Fable.Import.JS.JSON.stringify (Serializer.serializeEvent events.[i-1]))
        let! next = update cache.[i-1] events.[i-1] // cache[1] = update cache[0] events[0]
        cache.[i] <- next
        //printfn "evaluating: %d (done)" i
      repl.Reply(cache.[i])
  with e ->
    Browser.console.error("Agent failed: %O", e)
  })

let initialize () = async {
  let! data = data [ "aviation", "data/avia.csv"; "rail", "data/rail.csv" ]
  let external = [ "data", data; "chart", chart ]
  let initialCode =
    { Arguments = None; External = Map.ofList external; Values = Map.empty
      Counter = 0; Source = [] } 
  let initial =
    { Initial = initialCode; Code = initialCode; Program = []; CurrentFunction = None; Forward = []; Caption = None
      CurrentValue = None; CurrentName = None; CurrentReplace = None; CurrentCompletions = None; Modified = false;
      SelectedPath = None; HighlightedPath = None; SelectedMenuItem = None }
  return initial }

let createInteractive initial sheetMode id = async {
  try
    let codeScript = Browser.document.getElementById(id + "-source")
    let events = codeScript.innerText |> Serializer.deserializeEvents 
    let skipEvents = int (codeScript.dataset.["skipEvents"])
    let title = codeScript.dataset.["title"]
    let view = if sheetMode then viewSheet else viewCode
    
    let mutable clipped = false
    let unclipEvent = new Event<_>()
    let unclip () = 
      clipped <- false
      unclipEvent.Trigger()

    let trigger, setState, stateChanged = createVirtualDomAsyncApp (id + "-out") initial (view unclip id title) update
    stateChanged.Add(fun state -> clipped <- state.Modified)
    
    let agent = createEvalAgent (update trigger) initial events
    //printfn "%s has %d events" id events.Length
    createScrolly unclipEvent.Publish id 50 (events.Length - skipEvents + 1) (fun i -> Async.StartImmediate <| async {
      //printfn "scroll %s to %d" id i
      if not clipped then
        let! state = agent.PostAndAsyncReply(fun ch -> i + skipEvents, ch)
        setState { state with Modified = false }
    })
  with e ->
    Browser.console.error(e)
}


let jupyter = Array.init 24 (fun i -> "screens/jupyter/frame" + (i+1).ToString().PadLeft(3,'0') + ".png")
let gui = Array.init 474 (fun i -> "screens/gui/frame" + i.ToString().PadLeft(3,'0') + ".png")
createSlideshow 50 "screen1" jupyter
createSlideshow 10 "screen2" gui
()
Async.StartImmediate <| async {
  let! initial = initialize ()
  do! createInteractive initial false "scrolly1"
  do! createInteractive initial false "scrolly2"
  do! createInteractive initial true "scrolly3"
  do! createInteractive initial false "scrolly4"
}
