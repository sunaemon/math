module

public import PolishSpaceBook.FirstOrderLocalRuleCorrectness
public import PolishSpaceBook.FirstOrderEffectiveNullaryCorrectness
public import PolishSpaceBook.FirstOrderEffectiveUnaryCorrectness
public import PolishSpaceBook.FirstOrderEffectiveMultipleCorrectness

@[expose] public section

/-! # Arity dispatch for the actual local rule checker -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (P rootInput childInput rootInput_value childInput_value)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option backward.isDefEq.respectTransparency.types false

def GuardedCases (n : ℕ) (xs : List ℕ) : Prop :=
  let z := Nat.pair n (NatListCode.encode xs)
  match xs with
  | [] => (nullary rootInput).value z ≠ 0
  | [_] => (validSequent S (childInput 0)).value z ≠ 0 ∧
      (unary S rootInput (childInput 0)).value z ≠ 0
  | [_, _] => (validSequent S (childInput 0)).value z ≠ 0 ∧
      (validSequent S (childInput 1)).value z ≠ 0 ∧
      (binary S rootInput (childInput 0) (childInput 1)).value z ≠ 0
  | [_, _, _] => (validSequent S (childInput 0)).value z ≠ 0 ∧
      (validSequent S (childInput 1)).value z ≠ 0 ∧
      (validSequent S (childInput 2)).value z ≠ 0 ∧
      (ternary rootInput (childInput 0) (childInput 1) (childInput 2)).value z ≠ 0
  | _ => False

private theorem ifZero_value (p q r : P) (n : ℕ) :
    (p.ifZero q r).value n = if p.value n = 0 then q.value n else r.value n := rfl
private theorem equal_value (p q : P) (n : ℕ) :
    (p.equal q).value n = if p.value n = q.value n then 1 else 0 := rfl
private theorem mul_value (p q : P) (n : ℕ) :
    (p.mul q).value n = p.value n * q.value n := rfl
private theorem length_value (n : ℕ) (xs : List ℕ) :
    (LocalRulePrograms.Program.length Grammar.Program.ident.second).value (Nat.pair n (NatListCode.encode xs)) = xs.length := by
  simp [LocalRulePrograms.Program.length, LocalRulePrograms.Program.call, Grammar.Program.second, Grammar.Program.ident]

theorem checker_guarded_cases (n : ℕ) (xs : List ℕ) :
    (checker S).value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔
      (validSequent S rootInput).value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ∧ GuardedCases S n xs := by
  simp only [checker, LocalRulePrograms.Program.normalize_ne_zero, mul_value, Nat.mul_ne_zero_iff,
    ifZero_value, equal_value, length_value, Grammar.Program.const]
  cases xs with
  | nil => simp [GuardedCases, rootInput]
  | cons a xs =>
    cases xs with
    | nil => simp [GuardedCases, rootInput, childInput, LocalRulePrograms.Program.all, mul_value, Grammar.Program.const]
    | cons b xs =>
      cases xs with
      | nil => simp [GuardedCases, rootInput, childInput, LocalRulePrograms.Program.all, mul_value, Grammar.Program.const]
      | cons c xs =>
        cases xs with
        | nil => simp [GuardedCases, rootInput, childInput, LocalRulePrograms.Program.all, mul_value, Grammar.Program.const]
        | cons d xs => simp [GuardedCases]

theorem checker_rep_iff (n : ℕ) (xs : List ℕ) (s : Sequent L)
    (ss : List (Sequent L)) (hn : S.SequentRep n s)
    (hxs : List.Forall₂ (fun n s => S.SequentRep n s) xs ss) :
    (checker S).value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔ LocalRule ss s := by
  rw [checker_guarded_cases]
  have hv := (validSequent_correct S rootInput (Nat.pair n (NatListCode.encode xs))).mpr
    ⟨s, by simpa only [rootInput_value] using hn⟩
  apply (and_iff_right hv).trans
  cases hxs with
  | nil => exact nullary_iff S rootInput _ s (by simpa using hn)
  | @cons a s₀ xs ss h₀ hxs =>
    cases hxs with
    | nil =>
      rw [GuardedCases]
      have hp : S.SequentRep ((childInput 0).value (Nat.pair n (NatListCode.encode [a]))) s₀ := by simpa using h₀
      apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₀, hp⟩)).trans
      exact unary_iff S rootInput (childInput 0) _ s s₀ (by simpa using hn) hp
    | @cons b s₁ xs ss h₁ hxs =>
      cases hxs with
      | nil =>
        rw [GuardedCases]
        have hp : S.SequentRep ((childInput 0).value (Nat.pair n (NatListCode.encode [a,b]))) s₀ := by simpa using h₀
        have hq : S.SequentRep ((childInput 1).value (Nat.pair n (NatListCode.encode [a,b]))) s₁ := by simpa using h₁
        apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₀, hp⟩)).trans
        apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₁, hq⟩)).trans
        exact binary_iff S rootInput (childInput 0) (childInput 1) _ s s₀ s₁ (by simpa using hn) hp hq
      | @cons c s₂ xs ss h₂ hxs =>
        cases hxs with
        | nil =>
          rw [GuardedCases]
          have hp : S.SequentRep ((childInput 0).value (Nat.pair n (NatListCode.encode [a,b,c]))) s₀ := by simpa using h₀
          have hq : S.SequentRep ((childInput 1).value (Nat.pair n (NatListCode.encode [a,b,c]))) s₁ := by simpa using h₁
          have hr : S.SequentRep ((childInput 2).value (Nat.pair n (NatListCode.encode [a,b,c]))) s₂ := by simpa using h₂
          apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₀, hp⟩)).trans
          apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₁, hq⟩)).trans
          apply (and_iff_right ((validSequent_correct S _ _).mpr ⟨s₂, hr⟩)).trans
          exact ternary_iff S rootInput (childInput 0) (childInput 1) (childInput 2) _ s s₀ s₁ s₂ (by simpa using hn) hp hq hr
        | cons h₃ hxs =>
          change False ↔ _
          exact ⟨False.elim, fun h => by have hh := h.length_le_three; simp only [List.length_cons] at hh; omega⟩

theorem guardedCases_represented (n : ℕ) (xs : List ℕ) (h : GuardedCases S n xs) :
    ∃ ss : List (Sequent L),
      List.Forall₂ (fun a s => S.SequentRep a s) xs ss := by
  cases xs with
  | nil => exact ⟨[], .nil⟩
  | cons a xs =>
    cases xs with
    | nil =>
      obtain ⟨s, hs⟩ := (validSequent_correct S _ _).mp h.1
      have ha : S.SequentRep a s := by simpa only [childInput_value, List.getD_cons_zero] using hs
      exact ⟨[s], .cons ha .nil⟩
    | cons b xs =>
      cases xs with
      | nil =>
        obtain ⟨s, hs⟩ := (validSequent_correct S _ _).mp h.1
        obtain ⟨t, ht⟩ := (validSequent_correct S _ _).mp h.2.1
        have ha : S.SequentRep a s := by simpa using hs
        have hb : S.SequentRep b t := by simpa using ht
        exact ⟨[s,t], .cons ha (.cons hb .nil)⟩
      | cons c xs =>
        cases xs with
        | nil =>
          obtain ⟨s, hs⟩ := (validSequent_correct S _ _).mp h.1
          obtain ⟨t, ht⟩ := (validSequent_correct S _ _).mp h.2.1
          obtain ⟨u, hu⟩ := (validSequent_correct S _ _).mp h.2.2.1
          have ha : S.SequentRep a s := by simpa using hs
          have hb : S.SequentRep b t := by simpa using ht
          have hc : S.SequentRep c u := by simpa using hu
          exact ⟨[s,t,u], .cons ha (.cons hb (.cons hc .nil))⟩
        | cons d xs => exact False.elim h

/-- Every accepted raw input decodes to exactly the original local inference
relation. No well-formedness hypothesis is imposed on the supplied numbers. -/
theorem checker_represented_iff (n : ℕ) (xs : List ℕ) :
    (checker S).value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔
      ∃ s ss, S.SequentRep n s ∧
        List.Forall₂ (fun a t => S.SequentRep a t) xs ss ∧ LocalRule ss s := by
  constructor
  · intro h
    obtain ⟨hn, hxs⟩ := (checker_guarded_cases S n xs).mp h
    obtain ⟨s, hs⟩ := (validSequent_correct S _ _).mp hn
    have hs' : S.SequentRep n s := by simpa only [rootInput_value] using hs
    obtain ⟨ss, hss⟩ := guardedCases_represented S n xs hxs
    exact ⟨s, ss, hs', hss, (checker_rep_iff S n xs s ss hs' hss).mp h⟩
  · rintro ⟨s, ss, hs, hss, hr⟩
    exact (checker_rep_iff S n xs s ss hs hss).mpr hr

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Encode a context as a finite list of formula codes. Test equality of contexts by mutual membership up to
    $\alpha$-equivalence, so neither ordering nor repetition changes the test. Check all seventeen primitive rule
    alternatives, their exact numbers of premises, and their context conditions using the preceding finite searches.
-/
theorem checker_all_inputs_iff (z : ℕ) : (checker S).value z ≠ 0 ↔
    ∃ s ss, S.SequentRep z.unpair.1 s ∧
      List.Forall₂ (fun a t => S.SequentRep a t) (NatListCode.decode z.unpair.2) ss ∧ LocalRule ss s := by
  simpa only [NatListCode.encode_decode, Nat.pair_unpair] using
    checker_represented_iff S z.unpair.1 (NatListCode.decode z.unpair.2)


end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
