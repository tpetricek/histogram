module App

open Fable.PowerPack.Keyboard

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
  | OperationValue of (Reference list * Reference) option * (Value list -> Async<Value>)
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
  | _ when depth > 3 -> "(...)"
  | PrimitiveType p -> p
  | ObjectType(ot) -> sprintf "{ %s }" (String.concat ", " [for m, t in Seq.truncate 5 ot.Members -> m + ":" + formatType (depth+1) t])
  | OperationType(args, res) -> sprintf "(%s -> %s)" (String.concat ", " [for m, t in args -> m + ":" + formatType (depth+1) t]) (formatType (depth+1) res)

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
  { code with
      Source = code.Source @ [ (Indexed code.Counter, nexpr) ]
      Counter = code.Counter + 1 }

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
          let! vc = apply virtualCode interaction
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
      return { code with Source = nsource }

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
      return { code with Source = source; Values = values }

  | Evaluate(ref) ->
      let! _, values = evaluate code code.Values ref
      return { code with Values = values } }


// ------------------------------------------------------------------------------------------------
// User interface
// ------------------------------------------------------------------------------------------------

open Elmish
open Tbd.Html
open Tbd.Compost
open Fable.Core
open Fable.Import
open Fable.PowerPack

let renderTable headers data =
  h?div ["class"=>"table-container"] [
    h?table ["class"=>"data"] [
      yield h?tr [] [
        for hd in headers -> h?th [] [ text (string hd) ]
      ]
      for row in data -> h?tr [] [
        for col in row -> h?td [] [ text (string col) ]
      ]
    ]
  ]


type CodeState =
  { SelectedPath : Reference list option
    HighlightedPath : Reference list option
    SelectedMenuItem : int option }

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

    CodeState : CodeState
    }

type CodeEvent =
  | Select of Reference list option
  | Highlight of Reference list option
  | SelectMenu of int option

type Event =
  | Backward
  | Forward

  | Interact of Interaction
  | Refresh

  | UpdateCompletions of Reference option

  | UpdateCurrentFunction of Reference option

  | FinishReplace
  | UpdateReplace of (Reference * string) option

  | FinishAddValue
  | UpdateAddValue of string option

  | FinishNaming
  | UpdateName of (Reference * string) option

  | CodeEvent of CodeEvent

let interact op model = async {
  let! code = apply model.Code op
  printfn "Interacted: %A" op
  return { model with Program = model.Program @ [op]; Code = code; Forward = [] } }

let parse s =
  match System.Int32.TryParse(s) with
  | true, r -> PrimitiveType "number", PrimitiveValue r
  | _ -> PrimitiveType "string", PrimitiveValue s

let updateCode state = function
  | Select path -> { state with SelectedPath = path; SelectedMenuItem = None }
  | Highlight path -> { state with HighlightedPath = path }
  | SelectMenu item -> { state with SelectedMenuItem = item }

let update model evt = async {
  match evt with
  | CodeEvent ce ->
      let newCompletions = match ce with Select _ -> None | _ -> model.CurrentCompletions
      return { model with CodeState = updateCode model.CodeState ce; CurrentCompletions = newCompletions }

  | Forward ->
      let prog = List.head model.Forward :: model.Program
      let fwd = List.tail model.Forward
      let! code = apply model.Code (List.head model.Forward)
      return { model with Program = prog; Code = code; Forward = fwd }
  | Backward ->
      let prog, last = match List.rev model.Program with x::xs -> List.rev xs, x | _ -> failwith "Cannot go back"
      let fwd = last :: model.Forward
      let mutable code = model.Initial
      for op in prog do
        let! c = apply code op
        code <- c
      return { model with Program = prog; Forward = fwd; Code = code }

  | Refresh -> return model

  | UpdateCompletions ref ->
      let completions =
        if ref = Some(Indexed -1) then Some(Indexed -1, [])
        else ref |> Option.map (fun ref -> ref, getCompletions model.Code ref)
      return { model with CurrentCompletions = completions }

  | UpdateCurrentFunction f ->
      return { model with CurrentFunction = f }

  | UpdateReplace r ->
      return { model with CurrentReplace = r }
  | FinishReplace ->
      let ref, s = model.CurrentReplace.Value
      let t, v = parse s
      return! { model with CurrentReplace = None } |> interact (ReplaceValue(ref, v, t))

  | UpdateAddValue s ->
      return { model with CurrentValue = s }
  | FinishAddValue ->
      let t, v = parse (defaultArg model.CurrentValue "")
      return! { model with CurrentValue = None; CurrentCompletions = None } |> interact (DefineValue(v, t))

  | UpdateName(rn) ->
      return { model with CurrentName = rn }
  | FinishNaming ->
      match model.CurrentName with
      | Some(ref, n) -> return! { model with CurrentName = None } |> interact (Name(ref, n))
      | _ -> return failwith "Cannot finish naming when current name is none"

  | Interact i ->
      return! { model with CurrentCompletions = None } |> interact i }

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

        match getValue state k with
        | Some(v) ->
            yield renderPreview "preview" trigger v
        | None ->
            yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> trigger(Interact(Evaluate k)) ] [ text "evaluate" ]
            yield h?br [] []
        ]
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
  h?div [ "class" => "completions" ]
    [ for i, it in Seq.indexed items ->
        match it with
        | Element(ns, "a", attrs, children, render) ->
            let extras = [|
              if Some i = ctx.State.SelectedMenuItem  then yield "class" => "selected"
              yield "mouseover" =!> fun _ _ -> ctx.Trigger(CodeEvent(SelectMenu(Some i)))
            |]
            Element(ns, "a", Array.append extras attrs, children, render)
        | _ -> it ]

let renderSelectableBox ctx (path, ref) extras body =
  h?span [] [
    yield h?span
      [ yield "class" =>
          if pathStarts path ctx.State.SelectedPath then "expr selected"
          elif pathStarts path ctx.State.HighlightedPath then "expr highlighted"
          else "expr"
        yield "click" =!> fun _ e ->
          e.cancelBubble <- true
          if ctx.State.SelectedPath <> Some path then ctx.Trigger (CodeEvent(Select(Some path)))
        yield "mousemove" =!> fun _ e ->
          e.cancelBubble <- true
          if ctx.State.HighlightedPath <> Some path then ctx.Trigger (CodeEvent(Highlight(Some path)))
        yield! extras
      ] [
        body
        //h?ul ["style"=>"font-size:50%"] [
        //  yield h?li [] [ text (sprintf "[%s]" (formatType 0 (typeCheck ctx.AllState.Code ref))) ]
        //]
      ]
    if pathStarts path ctx.State.SelectedPath then
      yield h?div [ "style" => "display:inline-block" ] [
        yield h?button [
          "class" => "plus"
          "click" =!> fun _ e -> e.cancelBubble <- true; ctx.Trigger(UpdateCompletions(Some ref))
        ] [ text "+" ]
        match ctx.AllState.CurrentCompletions with
        | Some(k, compl) when Some path = ctx.State.SelectedPath && k = ref ->
            yield renderCompletions ctx [
              match ctx.AllState.CurrentName with
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

let rec renderReferencedExpression ctx (path, ref) : _ list =
  [ match ref, ctx.AllState.CurrentReplace with
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

let renderText trigger (state:Model) =
  let code = state.Code.Source
  let allRefs = code |> Seq.collect (snd >> collectReferences code) |> set
  let ctx = { Code = state.Code.Source; Trigger = trigger; Variables = Map.empty; AllState = state; State = state.CodeState }

  let code =
    h?div
      [ "class" => "code"
        "mousemove" =!> fun _ e ->
          e.cancelBubble <- true
          if state.CodeState.HighlightedPath <> None then trigger (CodeEvent(Highlight(None)))
        "mouseout" =!> fun _ e ->
          e.cancelBubble <- true
          if state.CodeState.HighlightedPath <> None then trigger (CodeEvent(Highlight(None)))
      ] [
        for ref, _ in code ->
          h?div ["class" => "indent"] [
            match ref, allRefs.Contains ref with
            | Named n, _ ->
                yield h?span [ "class" => "let" ] [ text ("let " + n + " = ") ]
                //yield renderReferencedExpression ctx ref
                yield h?div [ "class" => "indent" ] (renderExpression ctx ([ref], ref) (find ref ctx.Code))
                //yield h?span [ "class" => "indent" ] (renderReferencedExpression ctx ([ref], ref))

            | Indexed n, false ->
                yield h?span [ "class" => "let" ] [ text (sprintf "do[%d]" n) ]
                yield h?div [ "class" => "indent" ] (renderReferencedExpression ctx ([ref], ref))
            | _ -> ()
          ]
        yield h?div [ "class" => "indent" ] [
          yield h?span [ "class" => "let" ] [ text "do" ]
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
                  for (KeyValue(k, _)) in ctx.AllState.Code.External ->
                    h?a [ "href"=>"javascript:;"; "click" =!> fun _ _ -> ctx.Trigger(Interact(DefineExternal k)) ] [ text k ]
                ]
            | _ -> ()
          ]
        ]
      ]
  let preview =
    h?div [
      "id" => "preview"
      "click" =!> fun _ e -> e.cancelBubble <- true
    ] [
      match ctx.State.HighlightedPath, ctx.State.SelectedPath with
      | Some (ref::_), _
      | _, Some (ref::_) ->
          yield h?p [] [ text (sprintf "Highlighted: %A" ref) ]
          match getValue ctx.AllState ref with
          | Some(v) ->
              yield renderPreview "bigpreview" trigger v
          | None ->
              yield h?a [ "href"=>"javascript:;"; "click" =!> fun _ e -> e.cancelBubble <- true; trigger(Interact(Evaluate ref)) ] [ text "evaluate" ]
      | _ -> ()
    ]

  h?table [
      "class" => "split"
      "click" =!> fun _ e -> e.cancelBubble <- true; trigger (CodeEvent(Select(None)))
    ] [ h?tr [] [ h?td [] [ code ]; h?td [] [ preview ] ] ]
(*
  { Source : list<Reference * Expr>
    Values : Map<Reference, int * Value>
    Arguments : Map<string, Reference> option
    Counter : int
    Completions : (Reference * ((string * Completion) list)) option }
  []
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

  let serializeCodeEvent = function
    | Select(None) -> createObj [ "kind" => "noselect" ]
    | Highlight(None) -> createObj [ "kind" => "nohighlight" ]
    | SelectMenu(None) -> createObj [ "kind" => "nomenu" ]
    | Select(Some refs) -> createObj [ "kind" => "select"; "path" => Array.map serializeRef (Array.ofSeq refs) ]
    | Highlight(Some refs) -> createObj [ "kind" => "highlight"; "path" => Array.map serializeRef (Array.ofSeq refs) ]
    | SelectMenu(Some n) -> createObj [ "kind" => "menu"; "selected" => n ]

  let serializeEvent = function
    | Interact i -> createObj [ "kind" => "interact"; "interaction" => serializeInteraction i ]
    | CodeEvent c -> createObj [ "kind" => "code"; "event" => serializeCodeEvent c ]
    | Backward -> createObj [ "kind" => "backward" ]
    | Forward -> createObj [ "kind" => "forward" ]
    | Refresh -> createObj [ "kind" => "refresh" ]
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


  let deserializeCodeEvent obj =
    match obj?kind with
    | "noselect" -> Select(None)
    | "nohighlight" -> Highlight(None)
    | "nomenu" -> SelectMenu(None)
    | "select" -> Select(Some(List.ofArray (Array.map deserializeRef obj?path)))
    | "highlight" -> Highlight(Some(List.ofArray (Array.map deserializeRef obj?path)))
    | "menu" -> SelectMenu(Some obj?selected)
    | k -> failwithf "deserialize: Unexpected code event kind: %s" k

  let deserializeEvent obj =
    match obj?kind with
    | "interact" -> Interact (deserializeInteraction obj?interaction)
    | "code" -> CodeEvent(deserializeCodeEvent obj?event) 
    | "backward" -> Backward
    | "forward" -> Forward
    | "refresh" -> Refresh
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
  h?pre [ "class" => "source" ] [
    yield text "[\n"
    for e in events -> text ("  " + Fable.Import.JS.JSON.stringify(Serializer.serializeEvent e) + ",\n")
    yield text "]"
  ]

let view events trigger state =
  //Browser.console.log("PROGRAM")
  //for p in state.Program do Browser.console.log(" * ", string p)
  h?div [] [
    (*
    h?div [] [
      if not (List.isEmpty state.Program) then
        yield h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger Backward] [ text "<- Back" ]
      yield text (sprintf " (%d past interactions, %d forward) " state.Program.Length state.Forward.Length)
      if not (List.isEmpty state.Forward) then
        yield h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger Forward ] [ text "Forward ->" ]
    ]
    *)
    renderText trigger state
    //renderSheet trigger state
    renderSource events state
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
      member x.Preview _ = renderTable [ for (k, _), v in data -> k ] [[ for k, v in data -> v ]]
      member x.Lookup m =
        if m = "lookup" then OperationValue(None, fun [PrimitiveValue m] -> async {
          return data |> Seq.pick (fun (k, v) -> if k = unbox m then Some(PrimitiveValue v) else None) })
        else data |> Seq.pick (fun ((k, _), v) -> if k = m then Some(parse v) else None) }
  ObjectValue(row :> ObjectValue)

let sortByType keys resTyp =
  { new ObjectType with
      member x.Refine _ = x
      member x.Members =
        [ for k in keys do
            yield k + " ascending", resTyp
            yield k + " descending", resTyp ] } |> ObjectType

let frameValue (data:string[][]) =
  let inferType v = match System.Int32.TryParse(v) with true, _ -> PrimitiveType "number" | _ -> PrimitiveType "string"
  let headers = Array.map2 (fun h v -> h, inferType v) data.[0] data.[1]
  let rows = data.[1..] |> Array.map (fun a -> a, rowValue headers a)
  let rec v (rows:(string[] * Value)[]) =
    let fov =
      { new FrameObjectValue with
        member x.Headers = headers
        member x.Hash = hash [for _, (ObjectValue r) in rows -> r.Hash ]
        member x.Preview _ =
          h?div [] [
            h?p [] [ text (sprintf "Table with %d rows" rows.Length)]
            renderTable [ for k, _ in headers -> k ] (Seq.truncate 200 [for a, _ in rows -> a])
          ]
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
                member y.Preview a = x.Preview a
                member x.Lookup m =
                  let asc = m.EndsWith(" ascending")
                  let m = m.Replace(" ascending", "").Replace(" descending", "")
                  let index = headers |> Array.findIndex (fun (h, _) -> h = m)
                  let sort = if asc then Array.sortBy else Array.sortByDescending
                  rows |> sort (fun (data, _) -> data.[index]) |> v }
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
      member x.Preview _ =
        h?ul [] [
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
    member x.Preview _ =
      let colors = Seq.initInfinite (fun _ ->
        [ "#1f77b4"; "#ff7f0e"; "#2ca02c"; "#d62728"; "#9467bd";
          "#8c564b"; "#e377c2"; "#7f7f7f"; "#bcbd22"; "#17becf"; ]) |> Seq.concat

      let headers = (List.head rows).Headers |> Array.map fst
      let headers = List.tail rows |> List.fold (fun headers row ->
        headers |> Array.filter (fun h -> row.Headers |> Array.exists (fun (h2, _) -> h = h2))) headers
      let lookups = rows |> List.map (fun row -> dict (Seq.zip (Array.map fst row.Headers) row.Data)  )

      let viz =
        Shape.Layered [
          for h in headers do
          for clr, (n, v) in Seq.zip colors (Seq.indexed lookups) do
          let n, v = sprintf "%s (%d)" h n, float v.[h]
          let bar n = Shape.Padding((2., 0., 2., 1.), Derived.Bar(CO v, CA n))
          yield Shape.Style((fun s -> { s with Fill = Solid(1.0, HTML clr) }), bar n)
        ]
      let viz = Shape.Axes(false, false, true, true, viz)
      Compost.createSvg false false (500., 500.) viz
    member x.Lookup n =
      if n = "add series" then OperationValue(None, fun [ObjectValue row] -> async {
        return barChartValue [ yield! rows; yield row :?> RowObjectValue] })
      else
        failwithf "chart: member %s does not exist" n } |> ObjectValue

let chart =
  { new ObjectValue with
    member x.Hash = 0
    member x.Preview _ = h?div [] []
    member x.Lookup m =
      if m = "bar" then OperationValue(None, fun [ObjectValue row] -> async {
        return barChartValue [row :?> RowObjectValue] })
      else
        failwithf "chart: member %s does not exist" m } |> ObjectValue,
  { new ObjectType with
    member x.Refine _ = x
    member x.Members = ["bar", OperationType(["data", ObjectType(rowType [||])], barChartType) ] } |> ObjectType


let createScrolly id stepHeight stepCount trigger =
  let stepHeight, stepCount = float stepHeight, float stepCount
  let s = Browser.document.getElementById(id)
  let sb = Browser.document.getElementById(id + "-body")
  let hgt = Browser.window.innerHeight + stepHeight * stepCount
  s.style.height <- (string hgt) + "px"

  let old = Browser.window.onscroll
  Browser.window.onscroll <- fun e ->
    if unbox old <> null then old(e)
    if Browser.window.scrollY < s.offsetTop then
      sb.style.position <- "relative"
      sb.style.top <- "0px"
    elif Browser.window.scrollY > s.offsetTop + (stepHeight * stepCount) then
      sb.style.position <- "relative"
      sb.style.top <- string (stepHeight * stepCount) + "px"
    else
      let step = int ((Browser.window.scrollY - s.offsetTop) / stepHeight)
      trigger step
      sb.style.position <- "fixed"
      sb.style.top <- "0px"
      sb.style.width <- "100vw"
      sb.style.height <- (string Browser.window.innerHeight) + "px"

let images = Array.init 23 (fun i -> 
  let img = Browser.Image.Create()
  img.src <- "screens/jupyter/frame" + (i+1).ToString().PadLeft(3,'0') + ".png"
  img )

let captions = 
  let caps = Browser.document.getElementById("screen1-captions").innerText.Split([|'\r';'\n'|], System.StringSplitOptions.RemoveEmptyEntries)
  [| for cap in caps -> let r = cap.Split(':') in int r.[0], r.[1].Trim() |]

createScrolly "screen1" 100 23 (fun i ->
  let img = Browser.document.getElementById("screen1-frame")
  (unbox<Browser.HTMLImageElement> img).src <- images.[i].src
  let cap = Browser.document.getElementById("screen1-caption")
  cap.innerText <- captions |> Seq.takeWhile (fun (ci, _) -> ci <= i) |> Seq.last |> snd  
)

Async.StartImmediate <| async {
  try
    let! data = data [ "aviation", "data/avia.csv"; "rail", "data/rail.csv" ]
    let external = [ "data", data; "chart", chart ]
    let initial =
      { Arguments = None
        External = Map.ofList external
        Values = Map.empty
        Counter = 0
        Source = [] } // for n, _ in external -> Named n, External n ] }
        (*
    let prog = []
    let _prog = Serializer.deserializeProgram """
      [ {"kind":"value","value":2500,"type":"number"},
        {"kind":"dot","reference":"data","member":"aviation"},
        {"kind":"name","reference":1,"name":"avia"},
        {"kind":"dot","reference":"avia","member":"at"},
        {"kind":"apply","operation":2,"arguments":[["index",0]]},
        {"kind":"evaluate","reference":"avia"},
        {"kind":"dot","reference":3,"member":"victim"},
        {"kind":"value","value":"KIL","type":"string"},
        {"kind":"dot","reference":4,"member":"equals"},
        {"kind":"apply","operation":6,"arguments":[["other",5]]},
        {"kind":"evaluate","reference":7},
        {"kind":"abstract","arguments":[3],"output":7},
        {"kind":"dot","reference":"avia","member":"filter"},
        {"kind":"apply","operation":9,"arguments":[["predicate",8]]},
        {"kind":"dot","reference":7,"member":"and"},
        {"kind":"dot","reference":3,"member":"geo"},
        {"kind":"dot","reference":12,"member":"not equals"},
        {"kind":"value","value":"EU28","type":"string"},
        {"kind":"apply","operation":13,"arguments":[["other",14]]},
        {"kind":"apply","operation":11,"arguments":[["other",15]]},
        {"kind":"abstract","arguments":[3],"output":16},
        {"kind":"apply","operation":9,"arguments":[["predicate",17]]},
        {"kind":"evaluate","reference":18},
        {"kind":"dot","reference":"data","member":"rail"},
        {"kind":"evaluate","reference":19},
        {"kind":"dot","reference":19,"member":"at"},
        {"kind":"apply","operation":20,"arguments":[["index",0]]},
        {"kind":"evaluate","reference":21},
        {"kind":"dot","reference":21,"member":"victim"},
        {"kind":"dot","reference":22,"member":"equals"},
        {"kind":"apply","operation":23,"arguments":[["other",5]]},
        {"kind":"dot","reference":24,"member":"and"},
        {"kind":"dot","reference":21,"member":"accident"},
        {"kind":"evaluate","reference":26},
        {"kind":"value","value":"TOTAL","type":"string"},
        {"kind":"dot","reference":26,"member":"equals"},
        {"kind":"apply","operation":28,"arguments":[["other",27]]},
        {"kind":"apply","operation":25,"arguments":[["other",29]]},
        {"kind":"name","reference":19,"name":"rail"},
        {"kind":"dot","reference":21,"member":"pers_inv"},
        {"kind":"dot","reference":31,"member":"equals"},
        {"kind":"apply","operation":32,"arguments":[["other",27]]},
        {"kind":"dot","reference":30,"member":"and"},
        {"kind":"apply","operation":34,"arguments":[["other",33]]},
        {"kind":"dot","reference":21,"member":"geo"},
        {"kind":"dot","reference":36,"member":"not equals"},
        {"kind":"apply","operation":37,"arguments":[["other",14]]},
        {"kind":"dot","reference":35,"member":"and"},
        {"kind":"apply","operation":39,"arguments":[["other",38]]},
        {"kind":"abstract","arguments":[21],"output":40},
        {"kind":"dot","reference":"rail","member":"filter"},
        {"kind":"apply","operation":42,"arguments":[["predicate",41]]},
        {"kind":"evaluate","reference":43},
        {"kind":"dot","reference":18,"member":"sum"},
        {"kind":"dot","reference":43,"member":"sum"},
        {"kind":"evaluate","reference":44},
        {"kind":"evaluate","reference":45},
        {"kind":"name","reference":45,"name":"rail sums"},
        {"kind":"name","reference":44,"name":"avia sums"},
        {"kind":"dot","reference":"chart","member":"bar"},
        {"kind":"apply","operation":46,"arguments":[["data","avia sums"]]},
        {"kind":"evaluate","reference":47},
        {"kind":"apply","operation":46,"arguments":[["data","rail sums"]]},
        {"kind":"evaluate","reference":48},
        {"kind":"dot","reference":47,"member":"add series"},
        {"kind":"apply","operation":49,"arguments":[["data","rail sums"]]},
        {"kind":"evaluate","reference":50} ]"""
    let _prog =
      [ DefineValue (PrimitiveValue 2500,PrimitiveType "number")
        Complete (Dot (Named "data","aviation"))
        Name(Indexed 1, "avia")
        Complete (Dot (Named "avia","at"))
        Complete (Apply (Indexed 2,"index",Indexed 0))
        Evaluate (Named "avia")
        Complete (Dot (Indexed 3,"victim"))
        DefineValue (PrimitiveValue "KIL",PrimitiveType "string")
        Complete (Dot (Indexed 4,"equals"))
        Complete (Apply (Indexed 6,"other",Indexed 5))
        Evaluate (Indexed 7)
        Abstract ([Indexed 3],Indexed 7)
        Complete (Dot (Named "avia","filter"))
        Complete (Apply (Indexed 9,"predicate",Indexed 8))
      ]
    //let code = prog |> List.fold apply initial
    *)
    let initial =
      { Initial = initial; Code = initial; Program = []; CurrentFunction = None; Forward = [];
        CurrentValue = None; CurrentName = None; CurrentReplace = None; CurrentCompletions = None
        CodeState = { SelectedPath = None; HighlightedPath = None; SelectedMenuItem = None } }
    let setState = createVirtualDomAsyncApp "out" initial view update


    let createEvalAgent (events:_[]) = MailboxProcessor<_ * AsyncReplyChannel<_>>.Start(fun inbox -> async {
      let cache = System.Collections.Generic.Dictionary<_, _>()
      cache.[0] <- initial
      try
        while true do
          let! i, repl = inbox.Receive()
          let lastComputed = [i .. -1 .. 0] |> Seq.find (fun i -> printfn "checking %d: %b" i (cache.ContainsKey i); cache.ContainsKey i)
          for i in lastComputed+1 .. i do
            printfn "evaluating: %d, %s" i (Fable.Import.JS.JSON.stringify (Serializer.serializeEvent events.[i-1]))
            let! next = update cache.[i-1] events.[i-1] // cache[1] = update cache[0] events[0]
            cache.[i] <- next
            printfn "evaluating: %d (done)" i
          repl.Reply(cache.[i])
      with e ->
        Browser.console.error("Agent failed: %O", e)
      })

    let events =
      Browser.document.getElementById("scrolly1-source").innerText
      |> Serializer.deserializeEvents 

    let agent = createEvalAgent events
    createScrolly "scrolly1" 100 events.Length (fun i -> Async.StartImmediate <| async {
      let! state = agent.PostAndAsyncReply(fun ch -> i, ch)
      setState state
    })
  with e ->
    Browser.console.error(e)
}


