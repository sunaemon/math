module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import Mathlib.Tactic

@[expose] public section

register_simp_attr simp_lengths --seemingly not usable in file where declared
register_simp_attr simp_fixing
register_simp_attr simp_isPosition

open Lean Meta Elab Tactic Term

meta section simpAtStar
--modify getNondepPropHyps
def Lean.MVarId.getPropHyps (mvarId : MVarId) : MetaM (Array FVarId) := do
  mvarId.withContext do
  let mut result := #[]
  for ldecl in ← getLCtx do
    if !ldecl.isImplementationDetail && (← isProp ldecl.type) && !ldecl.hasValue then
      result := result.push ldecl.fvarId
  return result
--modify simpLocation
def simpLocationAtStar (ctx : Simp.Context)
  (simprocs : Simp.SimprocsArray)
  (discharge? : Option Simp.Discharge := none) :
  Tactic.TacticM Simp.Stats := do
    Tactic.withMainContext do
      go (← (← Tactic.getMainGoal).getPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) :
    TacticM Simp.Stats := do
    let mvarId ← getMainGoal
    let (result?, stats) ← simpGoal mvarId ctx (simprocs := simprocs)
      (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return stats
--variant of simp at * that also simplifies dependent hypotheses
syntax (name := simpAtStar) "simpAtStar" (Parser.Tactic.config)?
  (Parser.Tactic.discharger)? (&" only")?
  (" [" withoutPosition((Parser.Tactic.simpStar
    <|> Lean.Parser.Tactic.simpErase <|> Parser.Tactic.simpLemma),*,?) "]")? : tactic
set_option linter.unusedVariables false in
@[tactic simpAtStar] def evalSimpAtStar : Tactic :=
  fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper, simpArgs } ←
    mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocationAtStar ctx simprocs discharge?
  return stats.diag
end simpAtStar
