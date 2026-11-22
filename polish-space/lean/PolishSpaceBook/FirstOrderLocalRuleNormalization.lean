module

public import PolishSpaceBook.FirstOrderRawFormulaViews
public import PolishSpaceBook.FirstOrderRawQuantifierWitnesses
public import PolishSpaceBook.FirstOrderRawEqualityMatcher
public import PolishSpaceBook.FirstOrderLocalRuleCases

@[expose] public section

/-! # Numerical projections and Boolean alternatives of the concrete checker -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
namespace LocalRulePrograms

def rawField (first : Bool) (a : ℕ) : ℕ :=
  if first then (a / 3).unpair.1 else (a / 3).unpair.2
def rawLeft (a : ℕ) := rawField true (rawField false a)
def rawRight (a : ℕ) := rawField false (rawField false a)
def HasTag (a k : ℕ) : Prop := (Term.decode (rawField true a)).Alpha (tag k)

@[simp] theorem rawField_app (first : Bool) (a b : LTerm) :
    rawField first (Term.app a b).code = if first then a.code else b.code := by
  cases first <;> simp [rawField, Term.code, Nat.add_div]
@[simp] theorem rawField_lam (first : Bool) (x : ℕ) (a : LTerm) :
    rawField first (Term.lam x a).code = if first then x else a.code := by
  cases first <;> simp [rawField, Term.code, Nat.add_div]
@[simp] theorem rawLeft_binary (k a b : LTerm) : rawLeft (Term.app k (.app a b)).code = a.code := by
  simp [rawLeft]
@[simp] theorem rawRight_binary (k a b : LTerm) : rawRight (Term.app k (.app a b)).code = b.code := by
  simp [rawRight]
@[simp] theorem rawLeft_quant (k a : LTerm) (x : ℕ) : rawLeft (Term.app k (.lam x a)).code = x := by
  simp [rawLeft]
@[simp] theorem rawRight_quant (k a : LTerm) (x : ℕ) : rawRight (Term.app k (.lam x a)).code = a.code := by
  simp [rawRight]

def formulaTag : FOL → ℕ
  | .falsum => 0
  | .equal _ _ => 1
  | .rel _ _ => 2
  | .binary c _ _ => connectiveCode c
  | .quant q _ _ => quantifierCode q

theorem parsed_tag_iff {a : ℕ} {φ : FOL} (ha : parseCode a = some φ) (k : ℕ) :
    HasTag a k ↔ formulaTag φ = k := by
  have h := parsedShape_of_parse ha
  have hc := Term.code_decode a
  generalize he : Term.decode a = t at h hc ⊢
  rw [← hc]
  cases h <;> simp only [HasTag, rawField_app, ↓reduceIte, Term.decode_code, formulaTag] <;>
    exact alpha_tag_index_iff (by assumption) k

theorem formulaTag_binary_iff (A : FOL) (c : Connective) :
    formulaTag A = connectiveCode c ↔ ∃ φ ψ, A = .binary c φ ψ := by
  cases A with
  | falsum => cases c <;> simp [formulaTag, connectiveCode]
  | equal => cases c <;> simp [formulaTag, connectiveCode]
  | rel => cases c <;> simp [formulaTag, connectiveCode]
  | binary d => cases d <;> cases c <;> simp [formulaTag, connectiveCode]
  | quant q => cases q <;> cases c <;> simp [formulaTag, connectiveCode, quantifierCode]

theorem formulaTag_quant_iff (A : FOL) (q : Quantifier) :
    formulaTag A = quantifierCode q ↔ ∃ x φ, A = .quant q x φ := by
  cases A with
  | falsum => cases q <;> simp [formulaTag, quantifierCode]
  | equal => cases q <;> simp [formulaTag, quantifierCode]
  | rel => cases q <;> simp [formulaTag, quantifierCode]
  | binary c => cases c <;> cases q <;> simp [formulaTag, connectiveCode, quantifierCode]
  | quant r => cases r <;> cases q <;> simp [formulaTag, quantifierCode]

theorem formulaTag_equal_iff (A : FOL) : formulaTag A = 1 ↔ ∃ s t, A = .equal s t := by
  cases A with
  | falsum => simp [formulaTag]
  | equal => simp [formulaTag]
  | rel => simp [formulaTag]
  | binary c => cases c <;> simp [formulaTag, connectiveCode]
  | quant q => cases q <;> simp [formulaTag, quantifierCode]

theorem parsed_binary_fields {a : ℕ} {c : Connective} {φ ψ : FOL}
    (ha : parseCode a = some (.binary c φ ψ)) :
    parseCode (rawLeft a) = some φ ∧ parseCode (rawRight a) = some ψ := by
  obtain ⟨k, A, B, hcode, _, hA, hB⟩ := (parseCode_binary_iff _ _ _ _).mp ha
  have hc := congrArg Term.code hcode
  rw [Term.code_decode] at hc
  simp only [hc, rawLeft_binary, rawRight_binary, parseCode, Term.decode_code]
  exact ⟨hA, hB⟩

theorem parsed_quant_fields {a : ℕ} {q : Quantifier} {x : ℕ} {φ : FOL}
    (ha : parseCode a = some (.quant q x φ)) : rawLeft a = x ∧ parseCode (rawRight a) = some φ := by
  obtain ⟨k, A, hcode, _, hA⟩ := (parseCode_quant_iff _ _ _ _).mp ha
  have hc := congrArg Term.code hcode
  rw [Term.code_decode] at hc
  simpa only [hc, rawLeft_quant, rawRight_quant, parseCode, Term.decode_code, true_and] using hA

theorem parsed_equal_fields {a : ℕ} {s t : ForcingFormulas.membershipLanguage.Term ℕ}
    (ha : parseCode a = some (.equal s t)) :
    rawLeft a = (NamedLambda.Term.var (termName s)).code ∧ rawRight a = (NamedLambda.Term.var (termName t)).code := by
  obtain ⟨k, hcode, _⟩ := (parseCode_equal_iff _ _ _).mp ha
  have hc := congrArg Term.code hcode
  rw [Term.code_decode] at hc
  simp only [hc, rawLeft_binary, rawRight_binary, and_self]

namespace Program
@[simp] theorem all_nil_ne_zero (n : ℕ) : (all []).value n ≠ 0 := Nat.one_ne_zero
@[simp] theorem any_nil_ne_zero (n : ℕ) : ¬(any []).value n ≠ 0 := fun h => h rfl
@[simp] theorem all_cons_ne_zero (p : P) (ps : List P) (n : ℕ) :
    (all (p :: ps)).value n ≠ 0 ↔ p.value n ≠ 0 ∧ (all ps).value n ≠ 0 := by
  exact Nat.mul_ne_zero_iff
@[simp] theorem any_cons_ne_zero (p : P) (ps : List P) (n : ℕ) :
    (any (p :: ps)).value n ≠ 0 ↔ p.value n ≠ 0 ∨ (any ps).value n ≠ 0 := by
  change (if p.value n = 0 then (any ps).value n else 1) ≠ (0 : ℕ) ↔ _
  by_cases h : p.value n = 0 <;> simp [h]
@[simp] theorem normalize_ne_zero (p : P) (n : ℕ) :
    (normalize p).value n ≠ 0 ↔ p.value n ≠ 0 := by
  change (if p.value n = 0 then 0 else 1) ≠ (0 : ℕ) ↔ _
  by_cases h : p.value n = 0 <;> simp [h]
@[simp] theorem alpha_ne_zero (p q : P) (n : ℕ) :
    (p.alpha q).value n ≠ 0 ↔ (Term.decode (p.value n)).Alpha (Term.decode (q.value n)) := by
  simp [Grammar.Program.alpha]
@[simp] theorem equal_ne_zero (p q : P) (n : ℕ) :
    (p.equal q).value n ≠ 0 ↔ p.value n = q.value n := by
  simp [Grammar.Program.equal]
@[simp] theorem field_value (first : Bool) (p : P) (n : ℕ) :
    (field first p).value n = rawField first (p.value n) := rfl
@[simp] theorem left_value (p : P) (n : ℕ) : (left p).value n = rawLeft (p.value n) := rfl
@[simp] theorem right_value (p : P) (n : ℕ) : (right p).value n = rawRight (p.value n) := rfl
@[simp] theorem tagIs_ne_zero (p : P) (k n : ℕ) :
    (tagIs p k).value n ≠ 0 ↔ HasTag (p.value n) k := by
  simp only [tagIs, alpha_ne_zero, field_value, Grammar.Program.const, Term.decode_code, HasTag]
@[simp] theorem contextEqual_ne_zero (p q : P) (n : ℕ) :
    (contextEqual p q).value n ≠ 0 ↔ ContextPrograms.equalBit (p.value n) (q.value n) = true := by
  simp [contextEqual, EigenvariablePrograms.Program.contextEqual, TemplatePrograms.Program.binary]
end Program

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
