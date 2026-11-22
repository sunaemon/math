module

public import PolishSpaceBook.FirstOrderQuantifierInstances

@[expose] public section

/-! # Context grammar and eigenvariable tests by lambda programs -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm NamedFirstOrder
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false

namespace ContextPrograms
open TemplatePrograms

/-- The parameter is a variable name; the tested datum is one formula code. -/
def freeProgram : Grammar.Program :=
  Program.binary freeVariableTerm (fun e x => if x ∈ (Term.decode e).fv then 1 else 0)
    freeVariableTerm_closed freeVariableTerm_apply
    Grammar.Program.ident.second Grammar.Program.ident.first

def hasFree (x e : ℕ) : Bool := (NatListCode.decode e).any (fun a => decide (x ∈ (Term.decode a).fv))
def freeTerm : AlphaTerm := anyWithParameter freeProgram.term

theorem freeTerm_closed : freeTerm.Closed := anyWithParameter_closed freeProgram.computes.1

theorem freeTerm_apply (x e : ℕ) : Relation.ReflTransGen Beta
    (app (app freeTerm (numeral x)) (numeral e))
    (numeral (if hasFree x e then 1 else 0)) := by
  apply anyWithParameter_apply (p := fun x a => decide (x ∈ (Term.decode a).fv))
  convert freeProgram.computes using 1
  funext n
  simp only [freeProgram, Program.binary, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, id_eq, decide_eq_true_eq]
  rfl

theorem mem_context_fv (xs : List FOL) (x : ℕ) :
    x ∈ (context xs).fv ↔ ∃ φ ∈ xs, x ∈ φ.fv := by
  classical
  simp only [Context.fv, Finset.mem_biUnion, context, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, hx⟩
    exact ⟨φ, hφ, hx⟩
  · rintro ⟨φ, hφ, hx⟩
    exact ⟨AlphaFormula.mk φ, ⟨φ, hφ, rfl⟩, hx⟩

theorem hasFree_listCode (xs : List FOL) (x : ℕ) :
    hasFree x (listCode xs) = true ↔ x ∈ (context xs).fv := by
  rw [mem_context_fv]
  simp only [hasFree, listCode, NatListCode.decode_encode, List.any_eq_true, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, hx⟩
    exact ⟨φ, hφ, by simpa only [Term.decode_code, encode_fv] using hx⟩
  · rintro ⟨φ, hφ, hx⟩
    exact ⟨(encode φ).code, ⟨φ, hφ, rfl⟩, by simpa only [Term.decode_code, encode_fv] using hx⟩

theorem freeTerm_context (xs : List FOL) (x : ℕ) : Relation.ReflTransGen Beta
    (app (app freeTerm (numeral x)) (numeral (listCode xs)))
    (numeral (if x ∈ (context xs).fv then 1 else 0)) := by
  simpa only [hasFree_listCode] using freeTerm_apply x (listCode xs)

/-- Rejection of malformed formula fields is computed for every numerical list. -/
def invalidFormulaTerm : AlphaTerm := numericalCompose reverseZeroTerm Grammar.formulaTerm

theorem invalidFormulaTerm_computes : NumericalComputes invalidFormulaTerm
    (fun n => if (parseCode n).isNone then 1 else 0) := by
  unfold invalidFormulaTerm
  have h := reverseZero_computes.comp Grammar.formulaTerm_computes
  refine ⟨h.1, fun n => ?_⟩
  have hn := h.2 n
  dsimp only at hn ⊢
  cases hp : parseCode n <;> simpa only [hp, Option.isNone_none, Option.isNone_some,
    Option.isSome_none, Option.isSome_some, ↓reduceIte, Bool.false_eq_true, Nat.one_ne_zero] using hn

def grammarTerm : AlphaTerm := numericalCompose reverseZeroTerm (app listAnyTerm invalidFormulaTerm)
def wellFormed (e : ℕ) : Bool := !(NatListCode.decode e).any (fun n => (parseCode n).isNone)

theorem grammarTerm_computes : NumericalComputes grammarTerm
    (fun n => if wellFormed n then 1 else 0) := by
  unfold grammarTerm
  have hAny : NumericalComputes (app listAnyTerm invalidFormulaTerm)
      (fun n => if (NatListCode.decode n).any (fun a => (parseCode a).isNone) then 1 else 0) :=
    ⟨closed_app listAnyTerm_closed invalidFormulaTerm_computes.1,
      listAnyTerm_apply invalidFormulaTerm_computes.1 _ invalidFormulaTerm_computes.2⟩
  have h := reverseZero_computes.comp hAny
  refine ⟨h.1, fun n => ?_⟩
  have flip (b : Bool) : (if !b then 1 else 0 : ℕ) =
      (if (if b then 1 else 0 : ℕ) = 0 then 1 else 0) := by cases b <;> rfl
  have hn := h.2 n
  dsimp only at hn ⊢
  rw [← flip] at hn
  exact hn

theorem wellFormed_iff (e : ℕ) :
    wellFormed e = true ↔ ∀ a ∈ NatListCode.decode e, ∃ φ : FOL, (Term.decode a).Alpha (encode φ) := by
  simp only [wellFormed, Bool.not_eq_true', List.any_eq_false, Option.isNone_iff_eq_none]
  constructor
  · intro h a ha
    cases hp : parseCode a with
    | none => exact (h a ha hp).elim
    | some φ => exact ⟨φ, parse_sound _ _ hp⟩
  · intro h a ha
    obtain ⟨φ, hφ⟩ := h a ha
    obtain ⟨ψ, hp, _⟩ := parse_complete hφ
    simp only [parseCode, hp, reduceCtorEq, not_false_eq_true]

theorem member_le_listCode {a : ℕ} {xs : List ℕ} (ha : a ∈ xs) : a ≤ NatListCode.encode xs := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    have hb := Nat.left_le_pair b (NatListCode.encode xs)
    have ht := Nat.right_le_pair b (NatListCode.encode xs)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [NatListCode.encode]; omega
    · have := ih ha; simp only [NatListCode.encode]; omega

/-- A context's numerical list code bounds all of its free names. -/
theorem context_name_bound (xs : List FOL) {x : ℕ} (hx : x ∈ (context xs).fv) : x ≤ listCode xs := by
  obtain ⟨φ, hφ, hx⟩ := (mem_context_fv xs x).mp hx
  have hφbound := EqualityMatcher.syntaxName_le_code (encode φ)
    (EqualityMatcher.names_subset_syntaxNames φ (fv_subset_names φ hx))
  exact hφbound.trans (member_le_listCode (List.mem_map.mpr ⟨φ, hφ, rfl⟩))

end ContextPrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
