module

public import PolishSpaceBook.FirstOrderLocalNullaryCorrectness
public import PolishSpaceBook.FirstOrderLocalUnaryCorrectness
public import PolishSpaceBook.FirstOrderLocalMultipleCorrectness

@[expose] public section

/-! # Arity dispatch for the actual local rule checker -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
open NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
set_option backward.isDefEq.respectTransparency.types false

def rootInput : P := Grammar.Program.ident.first
def childInput (i : ℕ) : P := Program.get Grammar.Program.ident.second i

@[simp] theorem rootInput_value (n e : ℕ) : rootInput.value (Nat.pair n e) = n := by
  simp [rootInput, Grammar.Program.first, Grammar.Program.ident]
@[simp] theorem childInput_value (n : ℕ) (xs : List ℕ) (i : ℕ) :
    (childInput i).value (Nat.pair n (NatListCode.encode xs)) = xs.getD i 0 := by
  simp [childInput, Program.get, Program.call, Grammar.Program.second, Grammar.Program.ident,
    Grammar.Program.pair, Grammar.Program.const]

def GuardedCases (n : ℕ) (xs : List ℕ) : Prop :=
  let z := Nat.pair n (NatListCode.encode xs)
  match xs with
  | [] => (nullary rootInput).value z ≠ 0
  | [_] => (Program.validSequent (childInput 0)).value z ≠ 0 ∧
      (unary rootInput (childInput 0)).value z ≠ 0
  | [_, _] => (Program.validSequent (childInput 0)).value z ≠ 0 ∧
      (Program.validSequent (childInput 1)).value z ≠ 0 ∧
      (binary rootInput (childInput 0) (childInput 1)).value z ≠ 0
  | [_, _, _] => (Program.validSequent (childInput 0)).value z ≠ 0 ∧
      (Program.validSequent (childInput 1)).value z ≠ 0 ∧
      (Program.validSequent (childInput 2)).value z ≠ 0 ∧
      (ternary rootInput (childInput 0) (childInput 1) (childInput 2)).value z ≠ 0
  | _ => False

private theorem ifZero_value (p q r : P) (n : ℕ) :
    (p.ifZero q r).value n = if p.value n = 0 then q.value n else r.value n := rfl
private theorem equal_value (p q : P) (n : ℕ) :
    (p.equal q).value n = if p.value n = q.value n then 1 else 0 := rfl
private theorem mul_value (p q : P) (n : ℕ) :
    (p.mul q).value n = p.value n * q.value n := rfl
private theorem length_value (n : ℕ) (xs : List ℕ) :
    (Program.length Grammar.Program.ident.second).value (Nat.pair n (NatListCode.encode xs)) = xs.length := by
  simp [Program.length, Program.call, Grammar.Program.second, Grammar.Program.ident]

theorem checker_guarded_cases (n : ℕ) (xs : List ℕ) :
    checker.value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔
      (Program.validSequent rootInput).value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ∧ GuardedCases n xs := by
  simp only [checker, Program.normalize_ne_zero, mul_value, Nat.mul_ne_zero_iff,
    ifZero_value, equal_value, length_value, Grammar.Program.const]
  cases xs with
  | nil => simp [GuardedCases, rootInput]
  | cons a xs =>
    cases xs with
    | nil => simp [GuardedCases, rootInput, childInput, Program.all, mul_value, Grammar.Program.const]
    | cons b xs =>
      cases xs with
      | nil => simp [GuardedCases, rootInput, childInput, Program.all, mul_value, Grammar.Program.const]
      | cons c xs =>
        cases xs with
        | nil => simp [GuardedCases, rootInput, childInput, Program.all, mul_value, Grammar.Program.const]
        | cons d xs => simp [GuardedCases]

theorem checker_parsed_iff (n : ℕ) (xs : List ℕ) (s : Sequent membershipLanguage)
    (ss : List (Sequent membershipLanguage)) (hn : parseSequent n = some s)
    (hxs : List.Forall₂ (fun n s => parseSequent n = some s) xs ss) :
    checker.value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔ LocalRule ss s := by
  rw [checker_guarded_cases]
  have hv := (validSequent_ne_zero rootInput (Nat.pair n (NatListCode.encode xs))).mpr
    ⟨s, by simpa only [rootInput_value] using hn⟩
  apply (and_iff_right hv).trans
  cases hxs with
  | nil => exact nullary_ne_zero_iff rootInput _ (by simpa using hn)
  | @cons a s₀ xs ss h₀ hxs =>
    cases hxs with
    | nil =>
      rw [GuardedCases]
      have hp : parseSequent ((childInput 0).value (Nat.pair n (NatListCode.encode [a]))) = some s₀ := by simpa using h₀
      apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₀, hp⟩)).trans
      exact unary_iff rootInput (childInput 0) _ s s₀ (by simpa using hn) hp
    | @cons b s₁ xs ss h₁ hxs =>
      cases hxs with
      | nil =>
        rw [GuardedCases]
        have hp : parseSequent ((childInput 0).value (Nat.pair n (NatListCode.encode [a,b]))) = some s₀ := by simpa using h₀
        have hq : parseSequent ((childInput 1).value (Nat.pair n (NatListCode.encode [a,b]))) = some s₁ := by simpa using h₁
        apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₀, hp⟩)).trans
        apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₁, hq⟩)).trans
        exact binary_iff rootInput (childInput 0) (childInput 1) _ s s₀ s₁ (by simpa using hn) hp hq
      | @cons c s₂ xs ss h₂ hxs =>
        cases hxs with
        | nil =>
          rw [GuardedCases]
          have hp : parseSequent ((childInput 0).value (Nat.pair n (NatListCode.encode [a,b,c]))) = some s₀ := by simpa using h₀
          have hq : parseSequent ((childInput 1).value (Nat.pair n (NatListCode.encode [a,b,c]))) = some s₁ := by simpa using h₁
          have hr : parseSequent ((childInput 2).value (Nat.pair n (NatListCode.encode [a,b,c]))) = some s₂ := by simpa using h₂
          apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₀, hp⟩)).trans
          apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₁, hq⟩)).trans
          apply (and_iff_right ((validSequent_ne_zero _ _).mpr ⟨s₂, hr⟩)).trans
          exact ternary_iff rootInput (childInput 0) (childInput 1) (childInput 2) _ s s₀ s₁ s₂ (by simpa using hn) hp hq hr
        | cons h₃ hxs =>
          change False ↔ _
          exact ⟨False.elim, fun h => by have hh := h.length_le_three; simp only [List.length_cons] at hh; omega⟩

end PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
