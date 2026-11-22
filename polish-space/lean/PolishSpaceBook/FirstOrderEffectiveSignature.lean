module

public import PolishSpaceBook.FirstOrderLambdaGrammar

@[expose] public section

/-! # Effective first-order signatures with actual lambda realizers

Symbol codes include their arity. The recognizers return `arity + 1`, with
zero reserved for invalid codes. Each recognizer is an explicit closed lambda
term with its beta equation on every numerical input; this interface contains
no proof-checker oracle or assumption about derivability.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open FirstOrderLambdaEncoding.Grammar (Program)
universe u v

structure EffectiveSignature (L : Language.{u,v}) where
  functionCode : (Σ n, L.Functions n) → ℕ
  relationCode : (Σ n, L.Relations n) → ℕ
  decodeFunction : ℕ → Option (Σ n, L.Functions n)
  decodeRelation : ℕ → Option (Σ n, L.Relations n)
  decode_functionCode : ∀ f, decodeFunction (functionCode f) = some f
  decode_relationCode : ∀ r, decodeRelation (relationCode r) = some r
  functionCode_decode : ∀ c f, decodeFunction c = some f → functionCode f = c
  relationCode_decode : ∀ c r, decodeRelation c = some r → relationCode r = c
  functionArityProgram : Program
  relationArityProgram : Program
  functionArity_value : ∀ c, functionArityProgram.value c =
    match decodeFunction c with | none => 0 | some f => f.1 + 1
  relationArity_value : ∀ c, relationArityProgram.value c =
    match decodeRelation c with | none => 0 | some r => r.1 + 1

namespace EffectiveSignature
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem functionCode_injective : Function.Injective S.functionCode := by
  intro f g h
  have hh := congrArg S.decodeFunction h
  simpa only [S.decode_functionCode, Option.some.injEq] using hh

theorem relationCode_injective : Function.Injective S.relationCode := by
  intro r s h
  have hh := congrArg S.decodeRelation h
  simpa only [S.decode_relationCode, Option.some.injEq] using hh

theorem functionArity_apply (c : ℕ) : Relation.ReflTransGen Beta
    (app S.functionArityProgram.term (numeral c))
    (numeral (match S.decodeFunction c with | none => 0 | some f => f.1 + 1)) := by
  simpa only [S.functionArity_value] using S.functionArityProgram.computes.2 c

theorem relationArity_apply (c : ℕ) : Relation.ReflTransGen Beta
    (app S.relationArityProgram.term (numeral c))
    (numeral (match S.decodeRelation c with | none => 0 | some r => r.1 + 1)) := by
  simpa only [S.relationArity_value] using S.relationArityProgram.computes.2 c

theorem functionArity_code (n : ℕ) (f : L.Functions n) :
    S.functionArityProgram.value (S.functionCode ⟨n, f⟩) = n + 1 := by
  rw [S.functionArity_value, S.decode_functionCode]

theorem relationArity_code (n : ℕ) (r : L.Relations n) :
    S.relationArityProgram.value (S.relationCode ⟨n, r⟩) = n + 1 := by
  rw [S.relationArity_value, S.decode_relationCode]

theorem functionArity_eq_succ_iff (c n : ℕ) :
    S.functionArityProgram.value c = n + 1 ↔ ∃ f : L.Functions n, S.functionCode ⟨n, f⟩ = c := by
  rw [S.functionArity_value]
  cases h : S.decodeFunction c with
  | none =>
    simp only [Nat.zero_ne_add_one, false_iff, not_exists]
    intro f hf
    have hh := S.decode_functionCode ⟨n, f⟩
    rw [hf, h] at hh
    contradiction
  | some f =>
    rcases f with ⟨m, f⟩
    constructor
    · intro he
      change m + 1 = n + 1 at he
      have hmn : m = n := Nat.add_right_cancel he
      subst m
      exact ⟨f, S.functionCode_decode c ⟨n, f⟩ h⟩
    · rintro ⟨g, hg⟩
      have hh := S.decode_functionCode ⟨n, g⟩
      rw [hg, h] at hh
      exact congrArg (fun t : Σ k, L.Functions k => t.1 + 1) (Option.some.inj hh)

theorem relationArity_eq_succ_iff (c n : ℕ) :
    S.relationArityProgram.value c = n + 1 ↔ ∃ r : L.Relations n, S.relationCode ⟨n, r⟩ = c := by
  rw [S.relationArity_value]
  cases h : S.decodeRelation c with
  | none =>
    simp only [Nat.zero_ne_add_one, false_iff, not_exists]
    intro r hr
    have hh := S.decode_relationCode ⟨n, r⟩
    rw [hr, h] at hh
    contradiction
  | some r =>
    rcases r with ⟨m, r⟩
    constructor
    · intro he
      change m + 1 = n + 1 at he
      have hmn : m = n := Nat.add_right_cancel he
      subst m
      exact ⟨r, S.relationCode_decode c ⟨n, r⟩ h⟩
    · rintro ⟨s, hs⟩
      have hh := S.decode_relationCode ⟨n, s⟩
      rw [hs, h] at hh
      exact congrArg (fun t : Σ k, L.Relations k => t.1 + 1) (Option.some.inj hh)

/-- Code equality is implemented by the existing closed numerical equality
program and reflects equality of the symbols together with their arities. -/
theorem functionEquality_apply (f g : Σ n, L.Functions n) : Relation.ReflTransGen Beta
    (app (app equalityTerm (numeral (S.functionCode f))) (numeral (S.functionCode g)))
    (numeral (if S.functionCode f = S.functionCode g then 1 else 0)) :=
  equalityTerm_apply _ _

theorem functionEquality_correct (f g : Σ n, L.Functions n) :
    S.functionCode f = S.functionCode g ↔ f = g := S.functionCode_injective.eq_iff

theorem relationEquality_apply (r s : Σ n, L.Relations n) : Relation.ReflTransGen Beta
    (app (app equalityTerm (numeral (S.relationCode r))) (numeral (S.relationCode s)))
    (numeral (if S.relationCode r = S.relationCode s then 1 else 0)) :=
  equalityTerm_apply _ _

theorem relationEquality_correct (r s : Σ n, L.Relations n) :
    S.relationCode r = S.relationCode s ↔ r = s := S.relationCode_injective.eq_iff

end EffectiveSignature

open ForcingFormulas (membershipLanguage MembershipSymbol)
open FirstOrderLambdaEncoding.Grammar.Program

/-- The concrete membership signature has no function symbols and exactly
one binary relation, with code zero. All other numerical codes are rejected. -/
def membershipEffectiveSignature : EffectiveSignature membershipLanguage where
  functionCode f := nomatch f.2
  relationCode _ := 0
  decodeFunction _ := none
  decodeRelation c := if c = 0 then some ⟨2, MembershipSymbol.mem⟩ else none
  decode_functionCode f := nomatch f.2
  decode_relationCode r := by rcases r with ⟨n, r⟩; cases r; rfl
  functionCode_decode _ _ h := by cases h
  relationCode_decode c r h := by
    split_ifs at h with hc
    exact hc.symm
  functionArityProgram := const 0
  relationArityProgram := (equal ident (const 0)).ifZero (const 0) (const 3)
  functionArity_value _ := rfl
  relationArity_value c := by
    by_cases hc : c = 0 <;> simp [equal, ident, const, ifZero, hc]

end PolishSpaceBook.NamedFirstOrder
