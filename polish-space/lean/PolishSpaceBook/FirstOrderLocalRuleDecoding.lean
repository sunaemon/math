module

public import PolishSpaceBook.FirstOrderLocalRuleCorrectness

@[expose] public section

/-! # All-input correctness and malformed-label rejection for the local checker -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
open NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)

theorem guardedCases_decodes (n : ℕ) (xs : List ℕ) (h : GuardedCases n xs) :
    ∃ ss : List (Sequent membershipLanguage),
      List.Forall₂ (fun a s => parseSequent a = some s) xs ss := by
  cases xs with
  | nil => exact ⟨[], .nil⟩
  | cons a xs =>
    cases xs with
    | nil =>
      obtain ⟨s, hs⟩ := (validSequent_ne_zero _ _).mp h.1
      have ha : parseSequent a = some s := by simpa only [childInput_value, List.getD_cons_zero] using hs
      exact ⟨[s], .cons ha .nil⟩
    | cons b xs =>
      cases xs with
      | nil =>
        obtain ⟨s, hs⟩ := (validSequent_ne_zero _ _).mp h.1
        obtain ⟨t, ht⟩ := (validSequent_ne_zero _ _).mp h.2.1
        have ha : parseSequent a = some s := by simpa using hs
        have hb : parseSequent b = some t := by simpa using ht
        exact ⟨[s,t], .cons ha (.cons hb .nil)⟩
      | cons c xs =>
        cases xs with
        | nil =>
          obtain ⟨s, hs⟩ := (validSequent_ne_zero _ _).mp h.1
          obtain ⟨t, ht⟩ := (validSequent_ne_zero _ _).mp h.2.1
          obtain ⟨u, hu⟩ := (validSequent_ne_zero _ _).mp h.2.2.1
          have ha : parseSequent a = some s := by simpa using hs
          have hb : parseSequent b = some t := by simpa using ht
          have hc : parseSequent c = some u := by simpa using hu
          exact ⟨[s,t,u], .cons ha (.cons hb (.cons hc .nil))⟩
        | cons d xs => exact False.elim h

/-- Every accepted raw input decodes to exactly the original local inference
relation. No well-formedness hypothesis is imposed on the supplied numbers. -/
theorem checker_decoding_iff (n : ℕ) (xs : List ℕ) :
    checker.value (Nat.pair n (NatListCode.encode xs)) ≠ 0 ↔
      ∃ s ss, parseSequent n = some s ∧
        List.Forall₂ (fun a t => parseSequent a = some t) xs ss ∧ LocalRule ss s := by
  constructor
  · intro h
    obtain ⟨hn, hxs⟩ := (checker_guarded_cases n xs).mp h
    obtain ⟨s, hs⟩ := (validSequent_ne_zero _ _).mp hn
    have hs' : parseSequent n = some s := by simpa only [rootInput_value] using hs
    obtain ⟨ss, hss⟩ := guardedCases_decodes n xs hxs
    exact ⟨s, ss, hs', hss, (checker_parsed_iff n xs s ss hs' hss).mp h⟩
  · rintro ⟨s, ss, hs, hss, hr⟩
    exact (checker_parsed_iff n xs s ss hs hss).mpr hr

theorem checker_all_inputs_iff (z : ℕ) : checker.value z ≠ 0 ↔
    ∃ s ss, parseSequent z.unpair.1 = some s ∧
      List.Forall₂ (fun a t => parseSequent a = some t) (NatListCode.decode z.unpair.2) ss ∧ LocalRule ss s := by
  simpa only [NatListCode.encode_decode, Nat.pair_unpair] using
    checker_decoding_iff z.unpair.1 (NatListCode.decode z.unpair.2)

theorem checker_reject_root {z : ℕ} (h : parseSequent z.unpair.1 = none) : checker.value z = 0 := by
  by_contra hz
  obtain ⟨s, _, hs, _⟩ := (checker_all_inputs_iff z).mp hz
  rw [h] at hs
  contradiction

theorem checker_reject_child {z a : ℕ} (ha : a ∈ NatListCode.decode z.unpair.2)
    (h : parseSequent a = none) : checker.value z = 0 := by
  by_contra hz
  obtain ⟨_, ss, _, hss, _⟩ := (checker_all_inputs_iff z).mp hz
  have exists_label : ∀ {xs : List ℕ} {ts : List (Sequent membershipLanguage)},
      List.Forall₂ (fun a t => parseSequent a = some t) xs ts →
      ∀ a ∈ xs, ∃ t, parseSequent a = some t := by
    intro xs ts hh
    induction hh with
    | nil => simp
    | cons hc _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, hc⟩
      · exact ih a ha
  obtain ⟨t, ht⟩ := exists_label hss a ha
  rw [h] at ht
  contradiction

end PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
