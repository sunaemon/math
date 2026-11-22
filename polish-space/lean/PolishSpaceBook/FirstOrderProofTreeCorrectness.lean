module

public import PolishSpaceBook.FirstOrderProofTreeParsing
public import PolishSpaceBook.FirstOrderProofTreeState

@[expose] public section

/-! # The tree fold recognizes exactly the parsed locally checked trees

This proves the structural traversal and malformed-input rejection for the
actual local numerical program. The local-schema correspondence supplies the
separate link from these checks to first-order derivability.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
open NamedLambda
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency.types false

inductive Checked : Data → Prop where
  | node {s : ℕ} {cs : List Data} : validSeq s ≠ 0 →
      LocalRulePrograms.checker.value (Nat.pair s (NatListCode.encode (cs.map Data.root))) ≠ 0 →
      (∀ c ∈ cs, Checked c) → Checked (.node s cs)

/-- Successful parser views retain exactly the root fields held by the fold. -/
theorem parse_fields (M : LTerm) :
    (∀ T, (parse M).tree = some T → rootSeq (state M) = T.root) ∧
    (∀ cs, (parse M).children = some cs → rootList (state M) = NatListCode.encode (cs.map Data.root)) ∧
    (∀ p, (parse M).payload = some p → payloadRoot (state M) = p.1) := by
  induction M with
  | var x =>
    refine ⟨by simp [parse], ?_, by simp [parse]⟩
    intro cs hp
    by_cases hx : x = 0
    · simp only [parse, hx, ↓reduceIte, Option.some.injEq] at hp
      subst cs; simp only [rootList_state_var, List.map_nil, NatListCode.encode]
    · simp [parse, hx] at hp
  | lam x M ih => simp [parse]
  | app A B ihA ihB =>
    refine ⟨?_, ?_, ?_⟩
    · intro T hp
      obtain ⟨_, s, cs, hs, rfl⟩ := (parse_app_tree A B T).mp hp
      exact (rootSeq_state_app A B).trans (ihB.2.2 (s, cs) hs)
    · intro cs hp
      change ((parse A).tree.bind (fun T => (parse B).children.bind (fun ts => some (T :: ts)))) = some cs at hp
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
      obtain ⟨T, hT, ts, hts, rfl⟩ := hp
      rw [rootList_state_app, ihA.1 T hT, ihB.2.1 ts hts]
      rfl
    · intro p hp
      cases A with
      | var x =>
        change (parse B).children.map (fun cs => (x, cs)) = some p at hp
        obtain ⟨cs, _, rfl⟩ := Option.map_eq_some_iff.mp hp
        simp [Term.code]
      | app => simp [parse] at hp
      | lam => simp [parse] at hp

theorem tree_flag_iff (M : LTerm) :
    (treeBit (state M) ≠ 0 ↔ ∃ T, (parse M).tree = some T ∧ Checked T) ∧
    (listBit (state M) ≠ 0 ↔ ∃ cs, (parse M).children = some cs ∧ ∀ c ∈ cs, Checked c) ∧
    (payloadBit (state M) ≠ 0 ↔ ∃ s cs, (parse M).payload = some (s, cs) ∧
      validSeq s ≠ 0 ∧
      LocalRulePrograms.checker.value (Nat.pair s (NatListCode.encode (cs.map Data.root))) ≠ 0 ∧
      ∀ c ∈ cs, Checked c) := by
  induction M with
  | var x =>
    by_cases hx : x = 0 <;> simp [parse, hx]
  | lam x M ih => simp [parse]
  | app A B ihA ihB =>
    refine ⟨?_, ?_, ?_⟩
    · rw [treeBit_state_app, mul_ne_zero_iff]
      constructor
      · rintro ⟨htag, hp⟩
        have htag' : A.Alpha (tag 8) := by by_contra h; simp [h] at htag
        obtain ⟨s, cs, hparse, hs, hr, hcs⟩ := ihB.2.2.mp hp
        refine ⟨.node s cs, (parse_app_tree A B _).mpr ⟨htag', s, cs, hparse, rfl⟩, .node hs hr hcs⟩
      · rintro ⟨T, hp, hT⟩
        obtain ⟨htag, s, cs, hPayload, rfl⟩ := (parse_app_tree A B T).mp hp
        cases hT with
        | node hs hr hcs =>
          exact ⟨by simp [htag], ihB.2.2.mpr ⟨s, cs, hPayload, hs, hr, hcs⟩⟩
    · rw [listBit_state_app, mul_ne_zero_iff]
      constructor
      · rintro ⟨ht, hl⟩
        obtain ⟨T, hpT, hT⟩ := ihA.1.mp ht
        obtain ⟨cs, hpcs, hcs⟩ := ihB.2.1.mp hl
        refine ⟨T :: cs, ?_, ?_⟩
        · change ((parse A).tree.bind (fun T => (parse B).children.bind (fun cs => some (T :: cs)))) = _
          rw [hpT, hpcs]; rfl
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hT
          · exact hcs c hc
      · rintro ⟨cs, hp, hcs⟩
        change ((parse A).tree.bind (fun T => (parse B).children.bind (fun ts => some (T :: ts)))) = some cs at hp
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨T, hT, ts, hts, rfl⟩ := hp
        exact ⟨ihA.1.mpr ⟨T, hT, hcs T (by simp)⟩,
          ihB.2.1.mpr ⟨ts, hts, fun c hc => hcs c (by simp [hc])⟩⟩
    · cases A with
      | var s =>
        rw [payloadBit_state_app]
        have hdiv : 3 * s / 3 = s := by omega
        simp only [Term.code, Nat.mul_mod_right, ↓reduceIte, hdiv,
          Nat.one_mul, mul_ne_zero_iff]
        constructor
        · rintro ⟨⟨hl, hs⟩, hr⟩
          obtain ⟨cs, hp, hcs⟩ := ihB.2.1.mp hl
          rw [(parse_fields B).2.1 cs hp] at hr
          refine ⟨s, cs, ?_, hs, hr, hcs⟩
          change (parse B).children.map (fun cs => (s, cs)) = _
          rw [hp]; rfl
        · rintro ⟨s', cs, hp, hs, hr, hcs⟩
          change (parse B).children.map (fun cs => (s, cs)) = some (s', cs) at hp
          obtain ⟨ts, hts, he⟩ := Option.map_eq_some_iff.mp hp
          have he' : s = s' ∧ ts = cs := Prod.mk.inj he
          rcases he' with ⟨hss, htscs⟩
          subst s'
          subst ts
          rw [← (parse_fields B).2.1 cs hts] at hr
          exact ⟨⟨ihB.2.1.mpr ⟨cs, hts, hcs⟩, hs⟩, hr⟩
      | app C D => simp [payloadBit_state_app, Term.code, parse]
      | lam x C => simp [payloadBit_state_app, Term.code, parse]

/-- Acceptance on arbitrary natural numbers includes successful structural parsing. -/
theorem accepts_iff_parsed_checked (n : ℕ) :
    accepts n ↔ ∃ T, parseCode n = some T ∧ Checked T := (tree_flag_iff (Term.decode n)).1

/-- An invalid tree shape is rejected by the actual closed lambda program. -/
theorem checker_reject_malformed (n : ℕ) (hn : parseCode n = none) :
    Relation.ReflTransGen AlphaTerm.Beta
      (AlphaTerm.app checker.term (AlphaTerm.numeral n)) (AlphaTerm.numeral 0) := by
  have h : ¬accepts n := by
    intro ha
    obtain ⟨T, hp, _⟩ := (accepts_iff_parsed_checked n).mp ha
    simp [hn] at hp
  simpa only [h, ↓reduceIte] using checker_apply n

/-- On the advertised finite inputs, the program checks every node and descendant. -/
theorem accepts_encode_iff (T : Data) : accepts T.encode.code ↔ Checked T := by
  rw [accepts_iff_parsed_checked, parseCode_encode]
  simp only [Option.some.injEq, exists_eq_left']

end PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
