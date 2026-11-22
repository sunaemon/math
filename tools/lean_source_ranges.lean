import Lean
import Lean.Elab.Frontend

open Lean Meta Elab

-- Read-only index of original elaborated syntax. Proof terms are excluded:
-- the viewer needs mathematical expressions, not every proof subexpression.
private partial def kernelTree (e : Expr) (fuel : Nat := 1024) : MetaM Json := do
  if fuel == 0 then return Json.mkObj [("kind", toJson "truncated")]
  let next := fuel - 1
  match e with
  | .const name levels => return Json.mkObj [("kind", toJson "constant"),
      ("name", toJson name.toString), ("levels", toJson (reprStr levels))]
  | .app .. => return Json.mkObj [("kind", toJson "application"),
      ("function", ← kernelTree e.getAppFn next),
      ("arguments", toJson (← e.getAppArgs.mapM fun a => kernelTree a next))]
  | .fvar id => return Json.mkObj [("kind", toJson "variable"),
      ("name", toJson (← id.getDecl).userName.toString)]
  | .mdata _ body => kernelTree body next
  | .proj name index body => return Json.mkObj [("kind", toJson "projection"),
      ("structure", toJson name.toString), ("index", toJson index), ("value", ← kernelTree body next)]
  | .bvar index => return Json.mkObj [("kind", toJson "boundVariable"), ("index", toJson index)]
  | .lam name ty body bi => withLocalDecl name bi ty fun x => do
      return Json.mkObj [("kind", toJson "lambda"), ("name", toJson name.toString),
        ("domain", ← kernelTree ty next), ("body", ← kernelTree (body.instantiate1 x) next)]
  | .forallE name ty body bi => withLocalDecl name bi ty fun x => do
      return Json.mkObj [("kind", toJson "forall"), ("name", toJson name.toString),
        ("domain", ← kernelTree ty next), ("body", ← kernelTree (body.instantiate1 x) next)]
  | .letE name ty value body _ => withLetDecl name ty value fun x => do
      return Json.mkObj [("kind", toJson "let"), ("name", toJson name.toString),
        ("domain", ← kernelTree ty next), ("value", ← kernelTree value next),
        ("body", ← kernelTree (body.instantiate1 x) next)]
  | _ => return Json.mkObj [("kind", toJson "other"), ("expression", toJson (reprStr e))]

private def inspectTerm (ctx : ContextInfo) (term : TermInfo)
    (heads variables : Array String) : IO (Option Json) := do
  let some start := term.stx.getPos? | return none
  let some stop := term.stx.getTailPos? | return none
  if start >= stop then return none
  match term.stx.getHeadInfo with
  | .original .. => pure ()
  | _ => return none
  ctx.runMetaM term.lctx do
    let e ← instantiateMVars term.expr
    if e.hasMVar || (← isProof e) then return none
    let wanted ← match e.getAppFn with
      | .const name _ => pure (heads.contains name.toString)
      | .fvar id => pure (variables.contains (← id.getDecl).userName.toString)
      | _ => pure false
    if !wanted then return none
    let mut locals := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      locals := locals.push <| Json.mkObj [
        ("name", toJson decl.userName.toString),
        ("type", toJson (← ppExpr (← instantiateMVars decl.type)).pretty),
        ("value", toJson (← decl.value?.mapM fun v => return (← ppExpr (← instantiateMVars v)).pretty))]
    return some <| Json.mkObj [
      ("declaration", toJson (ctx.parentDecl?.map Name.toString)),
      ("startByte", toJson start.byteIdx), ("endByte", toJson stop.byteIdx),
      ("kernel", ← kernelTree e), ("locals", toJson locals)]

unsafe def main (args : List String) : IO UInt32 := do
  let [sourceFile, moduleName, queryFile, outputFile] := args
    | throw <| IO.userError "source-ranges SOURCE MODULE QUERY OUTPUT"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let query ← match Json.parse (← IO.FS.readFile queryFile) with
    | .ok value => pure value
    | .error err => throw <| IO.userError err
  let getArray (key : String) : IO (Array String) :=
    match query.getObjValAs? (Array String) key with
    | .ok value => pure value
    | .error err => throw <| IO.userError err
  let declarations ← getArray "declarations"
  let heads ← getArray "heads"
  let variables ← getArray "variables"
  let input ← IO.FS.readFile sourceFile
  let inputCtx := Parser.mkInputContext input sourceFile
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := ({} : Options).set `maxRecDepth (8192 : Nat) |>.setBool `Elab.async false
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := moduleName.toName)
  let state ← Lean.Elab.IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toList do
      if message.severity == .error then IO.eprintln (← message.toString)
    return 1
  let mut ranges := #[]
  for tree in state.commandState.infoState.trees.toArray do
    ranges ← tree.foldInfoM (init := ranges) fun ctx info result => do
      if !declarations.contains (ctx.parentDecl?.map Name.toString |>.getD "") then return result
      let .ofTermInfo term := info | return result
      try
        match ← inspectTerm ctx term heads variables with
        | some value => return result.push value
        | none => return result
      catch _ => return result
  IO.FS.writeFile outputFile (Json.compress (Json.mkObj [("ranges", toJson ranges)]))
  return 0
