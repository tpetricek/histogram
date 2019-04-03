module App
 
type Path = 
  | Path of int list

type Type = 
  | Object of (string * Type) list
  | Primitive of string
  | Any

type Node<'T> =
  { Node : 'T 
    Type : Type
    Completions : Interaction list option }

and Expr = 
  | Reference of string
  | Member of Node<Expr> * string
  | Hole

and Interaction =
  | Complete of Path
  | Choose of Path * int
  | Fill of Path * string // Fill Hole with Reference
  | Dot of Path * string // Dot completion on path

type Command = 
  | Let of string * Node<Expr> * Node<Expr>
  | Do of Node<Expr>

type Program = 
  | Program of Node<Command> list

type Value = 
  | Record of (string * Value) list
  | Value of obj

type Context = 
  { Globals : Map<string, Value * Type> }

type FindResult = 
  | FoundExpr of Node<Expr> * (Node<Expr> -> Program)
  | FoundCmd of Node<Command> * (Node<Command> -> Program)

let find program path =
  let rec findExpr n path =
    match n.Node, path with
    | _, [] -> n, id
    | Member(n, s), 0::path -> 
        let res, resf = findExpr n path
        res, fun repl -> { Node = Member(resf repl, s); Type = Any; Completions = None } // TODO: TC
    | _ -> failwith "Invalid path"

  match program, path with
  | Program cmds, Path(i::j::path) when i >= 0 && i < cmds.Length ->
      let result nd ct =
        let res, resf = findExpr nd path
        res, fun repl -> 
          let repl = resf repl 
          { Node = ct repl; Type = repl.Type; Completions = None }
      let res, resf = 
        match cmds.[i].Node, j with 
        | Do(n), 0 -> result n Do
        | Let(v, a, b), 0 -> result a (fun a -> Let(v, a, b))
        | Let(v, a, b), 1 -> result a (fun b -> Let(v, a, b))
        | _ -> failwith "Invalid path" 
      FoundExpr(res, fun repl ->       
        // TODO: type check references to replaced variable
        Program(List.mapi (fun idx cmd -> if idx = i then resf repl else cmd) cmds))
  | Program cmds, Path [i] when i >= 0 && i < cmds.Length ->
      FoundCmd(cmds.[i], fun repl ->
        Program(List.mapi (fun idx cmd -> if idx = i then repl else cmd) cmds))

  | _ -> failwith "Invalid path"

let (|Lookup|_|) key =
  List.tryPick (fun (k, v) -> if k = key then Some v else None)

let getExpr = function  
  | FoundExpr(e, f) -> e, f
  | _ -> failwith "Interaction cannot be used on a command"

let rec apply ctx program interaction =
  match interaction with
  | Fill(path, ref) ->
      let nd, f = find program path |> getExpr
      match nd.Node with 
      | Hole -> 
          match ctx.Globals.TryFind ref with
          | Some(_, t) -> f { Node = Reference ref; Type = t; Completions = None }
          | _ -> failwithf "Attempted to fill hole with non-existent reference %s" ref
      | _ -> failwith "Attempted to fill non-hole sub-expression"

  | Dot(path, mem) ->
      let nd, f = find program path |> getExpr
      match nd.Type with 
      | Object(Lookup mem memTy) -> 
          f { Node = Member({ nd with Completions = None }, mem); Type = memTy; Completions = None }
      | _ -> failwith "Not an object or object missing member"

  | Choose(path, i) -> 
      let nd, _ = find program path |> getExpr
      match nd.Completions with
      | Some compl when i >= 0 && i < compl.Length ->
          apply ctx program compl.[i]
      | _ -> failwith "Choosing completion that does not exist"

  | Complete(path) ->
      match find program path with
      | FoundCmd(nd, f) ->
          let completions = []
          f { nd with Completions = Some completions }
      | FoundExpr(nd, f) ->
          let completions = 
            match nd with 
            | { Node = Hole } -> [ for g, _ in Map.toSeq ctx.Globals -> Fill(path, g) ]
            | { Type = Object mems } -> [ for n, t in mems -> Dot(path, n) ]         
            | _ -> [] //  TODO: Not sure how to get completions on this...
          f { nd with Completions = Some completions }

let node t n = { Node = n; Type = t; Completions = None }
let empty = Program [ node Any (Do (node Any Hole)) ]

let person name year = 
  Record ["name", Value name; "year", Value year],
  Object ["name", Primitive "string"; "year", Primitive "int" ] 

let ctx = { Globals = Map.ofSeq ["tomas", person "Tomas" 1985; "jm", person "JM" 2017] }

let prog = 
  [ Complete(Path [0; 0]) 
    Choose(Path [0; 0], 0)
    Complete(Path [0; 0])
    Choose(Path [0; 0], 0) ]
  |> List.fold (apply ctx) empty

(*
  [ Complete(Path [0]) ]
  |> List.fold (apply ctx) empty
*)


(*


*)





open Elmish
open Tbd.Html

type Model = 
  { Program : Program 
    Context : Context }

let initial = { Program = empty; Context = ctx }

type Event = 
  | Interact of Interaction

let update model = function
  | Interact i -> { model with Program = apply model.Context model.Program i }

let cols els = 
  h?table [] [
    h?tr [] [ for e in els -> h?td [] [ e ] ]
  ]
let rows els = 
  h?table [] [ 
    for e in els -> h?tr [] [ h?td [] [ e ] ] 
  ]

let renderNode trigger nd path body =
  let expand = 
    h?button 
      [ "style" => "float:left"
        "click" =!> fun _ _ -> trigger (Interact (Complete(Path(List.rev path)))) ] [ text "..." ] 
  let completions compl = 
    [ for c in compl -> 
        h?button 
          [ "click" =!> fun _ _ -> trigger (Interact c) ] 
          [text (sprintf "%A" c)] ]

  h?div [ "style" => "border:1px solid black" ] 
    [ cols [
        ( match nd.Completions with 
          | None -> expand
          | Some compl -> rows (completions compl) )
        body
      ] ]
    
let rec renderExpr trigger e path = 
  match e.Node with 
  | Hole -> text "_"
  | Reference ref -> text ref
  | Member(e, mem) -> cols [ renderExpr trigger e (0::path); text mem ]
  |> renderNode trigger e path 

let renderCommand trigger cmd path = 
  match cmd.Node with
  | Do(e) ->
      cols
        [ h?strong[] [text "do"]
          renderExpr trigger e (0::path) ]

  | Let(v, a, b) ->
      cols
        [ h?strong[] [text "let"]
          renderExpr trigger a (0::path)
          h?strong[] [text "in"]
          renderExpr trigger b (1::path) ]
  |> renderNode trigger cmd path              
        
let renderProgram trigger (Program cmds) = 
  cmds 
  |> List.mapi (fun i cmd -> renderCommand trigger cmd [i])
  |> rows

let view trigger state =
  renderProgram trigger state.Program

createVirtualDomApp "out" initial view update 