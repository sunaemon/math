module

public import PolishSpaceBook.FirstOrderLambdaGrammar
public import PolishSpaceBook.FirstOrderNaturalDeduction
public import PolishSpaceBook.LambdaFiniteLists

@[expose] public section

/-! # Lambda comparison of contexts as finite sets of alpha classes

Lists are numerical data. Membership compares formulas modulo alpha, and context
equality checks mutual inclusion, so neither duplicates nor order matter.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm NamedFirstOrder
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false

namespace ContextPrograms

/-- Run a parameterized predicate on each entry of a numerical list. -/
def anyWithParameter (F : AlphaTerm) : AlphaTerm := lam 42
  (app listAnyTerm (app (curryNumerical F) (var 42)))

theorem anyWithParameter_closed {F : AlphaTerm} (hF : F.Closed) :
    (anyWithParameter F).Closed := by
  unfold anyWithParameter Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [listAnyTerm_closed, curryNumerical_closed hF]
  simp

theorem anyWithParameter_apply {F : AlphaTerm} {p : ℕ → ℕ → Bool}
    (hF : NumericalComputes F (fun n => if p n.unpair.1 n.unpair.2 then 1 else 0))
    (a e : ℕ) : Relation.ReflTransGen Beta
      (app (app (anyWithParameter F) (numeral a)) (numeral e))
      (numeral (if (NatListCode.decode e).any (p a) then 1 else 0)) := by
  have hc : (app (curryNumerical F) (numeral a)).Closed :=
    closed_app (curryNumerical_closed hF.1) (numeral_closed a)
  have hs : Beta (app (anyWithParameter F) (numeral a))
      (app listAnyTerm (app (curryNumerical F) (numeral a))) := by
    simpa only [anyWithParameter, subst_app, subst_var, ↓reduceIte,
      subst_closed _ _ _ listAnyTerm_closed,
      subst_closed _ _ _ (curryNumerical_closed hF.1)] using
      Beta.contract 42 (app listAnyTerm (app (curryNumerical F) (var 42))) (numeral a)
  apply (Relation.ReflTransGen.single (.app_left _ hs)).trans
  apply listAnyTerm_apply hc (p a)
  intro b
  exact (curryNumerical_apply hF.1 a b).trans (by simpa using hF.2 (Nat.pair a b))

def alphaTest : Grammar.Program := Grammar.Program.alpha
  Grammar.Program.ident.first Grammar.Program.ident.second

def member (a e : ℕ) : Bool :=
  (NatListCode.decode e).any (fun b => decide ((Term.decode a).Alpha (Term.decode b)))

def memberTerm : AlphaTerm := anyWithParameter alphaTest.term

theorem memberTerm_closed : memberTerm.Closed := anyWithParameter_closed alphaTest.computes.1

theorem memberTerm_apply (a e : ℕ) : Relation.ReflTransGen Beta
    (app (app memberTerm (numeral a)) (numeral e))
    (numeral (if member a e then 1 else 0)) := by
  apply anyWithParameter_apply (p := fun a b => decide ((Term.decode a).Alpha (Term.decode b)))
  convert alphaTest.computes using 1
  funext n
  simp only [alphaTest, Grammar.Program.alpha, Grammar.Program.first,
    Grammar.Program.second, Grammar.Program.ident, id_eq, decide_eq_true_eq]
  rfl


def memberProgram : Grammar.Program :=
  ⟨uncurryNumerical memberTerm, fun n => if member n.unpair.1 n.unpair.2 then 1 else 0,
    uncurryNumerical_computes memberTerm_closed _ memberTerm_apply⟩

/-- Parameter is the target context; each tested entry comes from the source. -/
def missingProgram : Grammar.Program :=
  let swapped := Grammar.Program.ident.second.pair Grammar.Program.ident.first
  ⟨numericalCompose reverseZeroTerm (numericalCompose memberProgram.term swapped.term),
    fun n => if member n.unpair.2 n.unpair.1 then 0 else 1, by
      have h := reverseZero_computes.comp (memberProgram.computes.comp swapped.computes)
      convert h using 1
      funext n
      simp only [memberProgram, swapped, Grammar.Program.pair, Grammar.Program.first,
        Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair]
      cases member n.unpair.2 n.unpair.1 <;> rfl⟩


def subset (e d : ℕ) : Bool :=
  !(NatListCode.decode e).any (fun a => !member a d)

/-- Arguments are target, source; the numerical wrapper below restores source,target. -/
def missingTerm : AlphaTerm := anyWithParameter missingProgram.term

theorem missingTerm_apply (d e : ℕ) : Relation.ReflTransGen Beta
    (app (app missingTerm (numeral d)) (numeral e))
    (numeral (if (NatListCode.decode e).any (fun a => !member a d) then 1 else 0)) := by
  apply anyWithParameter_apply (p := fun d a => !member a d)
  convert missingProgram.computes using 1
  funext n
  simp only [missingProgram]
  cases member n.unpair.2 n.unpair.1 <;> rfl

def subsetProgram : Grammar.Program :=
  let swapped := Grammar.Program.ident.second.pair Grammar.Program.ident.first
  let missing : Grammar.Program := ⟨uncurryNumerical missingTerm,
    fun n => if (NatListCode.decode n.unpair.2).any (fun a => !member a n.unpair.1) then 1 else 0,
    uncurryNumerical_computes (anyWithParameter_closed missingProgram.computes.1) _ missingTerm_apply⟩
  ⟨numericalCompose reverseZeroTerm (numericalCompose missing.term swapped.term),
    fun n => if subset n.unpair.1 n.unpair.2 then 1 else 0, by
      have h := reverseZero_computes.comp (missing.computes.comp swapped.computes)
      convert h using 1
      funext n
      simp only [missing, swapped, Grammar.Program.pair, Grammar.Program.first,
        Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair, subset]
      have flip (b : Bool) : (if !b then 1 else 0 : ℕ) =
          (if (if b then 1 else 0 : ℕ) = 0 then 1 else 0) := by cases b <;> rfl
      convert flip ((NatListCode.decode n.unpair.1).any (fun a => !member a n.unpair.2)) using 1
      rfl⟩

def equalProgram : Grammar.Program :=
  let swapped := Grammar.Program.ident.second.pair Grammar.Program.ident.first
  subsetProgram.mul ⟨numericalCompose subsetProgram.term swapped.term,
    fun n => if subset n.unpair.2 n.unpair.1 then 1 else 0,
    by
      convert subsetProgram.computes.comp swapped.computes using 1
      funext n
      simp only [subsetProgram, swapped, Grammar.Program.pair, Grammar.Program.first,
        Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair]⟩

theorem equalProgram_apply (e d : ℕ) : Relation.ReflTransGen Beta
    (app equalProgram.term (numeral (Nat.pair e d)))
    (numeral (if subset e d && subset d e then 1 else 0)) := by
  have h := equalProgram.computes.2 (Nat.pair e d)
  convert h using 1
  simp only [equalProgram, Grammar.Program.mul, subsetProgram, Nat.unpair_pair]
  cases subset e d <;> cases subset d e <;> rfl

noncomputable local instance contextFormulaDecidableEq : DecidableEq (AlphaFormula ForcingFormulas.membershipLanguage) :=
  Classical.decEq _

/-- Context representatives may have duplicate or alpha-equivalent entries. -/
noncomputable def context (xs : List FOL) : Context ForcingFormulas.membershipLanguage := by
  classical
  exact (xs.map AlphaFormula.mk).toFinset

def listCode (xs : List FOL) : ℕ := NatListCode.encode (xs.map (fun φ => (encode φ).code))

theorem member_listCode (φ : FOL) (xs : List FOL) :
    member (encode φ).code (listCode xs) = true ↔ AlphaFormula.mk φ ∈ context xs := by
  classical
  simp only [member, listCode, NatListCode.decode_encode, List.any_eq_true,
    List.mem_map, decide_eq_true_eq, Term.decode_code]
  constructor
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, hα⟩
    have he : AlphaFormula.mk φ = AlphaFormula.mk ψ :=
      (AlphaFormula.mk_eq_iff _ _).mpr ((encode_alpha_iff φ ψ).mp (by simpa using hα))
    simp only [context, List.mem_toFinset, List.mem_map]
    exact ⟨ψ, hψ, he.symm⟩
  · intro h
    obtain ⟨ψ, hψ, he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    refine ⟨(encode ψ).code, ⟨ψ, hψ, rfl⟩, ?_⟩
    simpa only [Term.decode_code, encode_alpha_iff] using (AlphaFormula.mk_eq_iff _ _).mp he.symm

theorem subset_listCode (xs ys : List FOL) :
    subset (listCode xs) (listCode ys) = true ↔ context xs ⊆ context ys := by
  classical
  simp only [subset, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_false,
    listCode, NatListCode.decode_encode, List.mem_map]
  constructor
  · intro h a ha
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact (member_listCode φ ys).mp (h _ ⟨φ, hφ, rfl⟩)
  · intro h a ha
    obtain ⟨φ, hφ, rfl⟩ := ha
    apply (member_listCode φ ys).mpr
    apply h
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨φ, hφ, rfl⟩)

/-- The actual closed lambda context comparator implements equality of finite
sets of alpha classes, independently of the representing list's order. -/
theorem equalProgram_context (xs ys : List FOL) :
    Relation.ReflTransGen Beta
      (app equalProgram.term (numeral (Nat.pair (listCode xs) (listCode ys))))
      (numeral (if context xs = context ys then 1 else 0)) := by
  classical
  have h := equalProgram_apply (listCode xs) (listCode ys)
  have he : (subset (listCode xs) (listCode ys) && subset (listCode ys) (listCode xs)) = true ↔
      context xs = context ys := by
    rw [Bool.and_eq_true, subset_listCode, subset_listCode]
    exact ⟨fun h => Finset.Subset.antisymm h.1 h.2, fun h => by simp [h]⟩
  simpa only [he] using h

end ContextPrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
