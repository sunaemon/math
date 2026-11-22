import PolishSpaceBook.LambdaComputablePointAssemblies
import Lean

open Lean Meta Elab Command
open PolishSpaceBook PolishSpaceBook.LambdaIndexPCA

-- These adapters check definitions, including domain membership and totality,
-- rather than merely comparing pretty-printed result types.
example (e : ℕ) (p : ℕ → ℕ) :
    ComputesName e p ↔ ∀ n, App e n (p n) := Iff.rfl

example {X : Type} (δ : Representation X) (x : X) :
    HasComputableName δ x ↔
      ∃ p : δ.domain, δ.toFun p = x ∧ ∃ e, ComputesName e p.val := Iff.rfl

example {X : Type} (δ : Representation X) (x : X) (hx : HasComputableName δ x) (e : ℕ) :
    e ∈ (computablePointAssembly δ).realizes ⟨x, hx⟩ ↔
      ∃ p : δ.domain, δ.toFun p = x ∧ ComputesName e p.val := Iff.rfl

private def shape (ty : Expr) : MetaM String := do
  if ← isDefEq ty (mkConst ``Nat) then return "Nat"
  if ← isDefEq ty (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) then return "Name"
  if ty == mkSort .zero then return "Prop"
  if ty.isSort then return "Carrier"
  if ty.isFVar then return "CarrierElement"
  if ty.getAppFn.isConstOf ``Representation then return "Representation"
  if ty.getAppFn.isConstOf ``Assembly then return "Assembly"
  return "unsupported"

run_cmd liftTermElabM do
  for name in [``ComputesName, ``HasComputableName, ``computablePointAssembly, ``Representation, ``Representation.mk] do
    let info ← getConstInfo name
    forallTelescope info.type fun xs result => do
      let mut binders : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        binders := binders.push <| Json.mkObj [
          ("name", toJson d.userName.toString),
          ("type", toJson (← ppExpr d.type).pretty),
          ("shape", toJson (← shape d.type))]
      let record := Json.mkObj [
        ("declaration", toJson name.toString),
        ("binders", toJson binders),
        ("result", toJson (← ppExpr result).pretty),
        ("resultShape", toJson (← shape result)),
        ("signature", toJson (reprStr info.type)),
        ("body", toJson (reprStr info.value?))]
      logInfo m!"SORT_PILOT {record.compress}"
