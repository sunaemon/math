module

public import PolishSpaceBook.FirstOrderEffectiveGrammarTags
public import PolishSpaceBook.FirstOrderEffectiveSyntax

@[expose] public section

/-! # Correctness of the effective-signature syntax recognizers

The simultaneous invariant reconstructs source terms, argument vectors and
formulas from every accepted raw lambda tree. Completeness uses the full
name-correspondence relation, so its quantifier step retains arbitrary binders.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding (LTerm tag node connectiveCode quantifierCode)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

private theorem payload_le_one (f : ℕ → ℕ) (a b : ℕ) : symbolPayload f a b ≤ 1 := by
  unfold symbolPayload
  split_ifs <;> omega

/-- Every Boolean field remains a bit, also on malformed raw inputs. -/
theorem state_bits (A : LTerm) :
    termBit (state S A) ≤ 1 ∧ functionPayloadBit (state S A) ≤ 1 ∧
    relationPayloadBit (state S A) ≤ 1 ∧ termPairBit (state S A) ≤ 1 ∧
    formulaBit (state S A) ≤ 1 ∧ binaryFormulaBit (state S A) ≤ 1 ∧
    quantFormulaBit (state S A) ≤ 1 := by
  induction A with
  | var x => simp [state]
  | lam x A ih => simp [state]; exact ih.2.2.2.2.1
  | app A B ihA ihB =>
    simp only [state, termBit_pack, functionPayloadBit_pack, relationPayloadBit_pack,
      termPairBit_pack, formulaBit_pack, binaryFormulaBit_pack, quantFormulaBit_pack]
    refine ⟨?_, payload_le_one _ _ _, payload_le_one _ _ _, ?_, ?_, ?_, by omega⟩
    · split_ifs <;> omega
    · exact (Nat.mul_le_mul ihA.1 ihB.1).trans (by decide)
    · unfold appFormula
      split_ifs <;> omega
    · exact (Nat.mul_le_mul ihA.2.2.2.2.1 ihB.2.2.2.2.1).trans (by decide)

private theorem function_payload_iff (a b : ℕ) :
    symbolPayload S.functionArityProgram.value a b = 1 ↔
      ∃ (n : ℕ) (f : L.Functions n), tagIndexPlus1 a = S.functionCode ⟨n, f⟩ + 1 ∧
        argsLenPlus1 b = n + 1 := by
  unfold symbolPayload
  constructor
  · intro h
    split_ifs at h with ht hf he
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hf
    obtain ⟨f, hcode⟩ := (S.functionArity_eq_succ_iff _ _).mp hn
    exact ⟨n, f, by omega, by omega⟩
  · rintro ⟨n, f, ht, hb⟩
    simp [ht, hb, S.functionArity_code]

private theorem relation_payload_iff (a b : ℕ) :
    symbolPayload S.relationArityProgram.value a b = 1 ↔
      ∃ (n : ℕ) (r : L.Relations n), tagIndexPlus1 a = S.relationCode ⟨n, r⟩ + 1 ∧
        argsLenPlus1 b = n + 1 := by
  unfold symbolPayload
  constructor
  · intro h
    split_ifs at h with ht hr he
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hr
    obtain ⟨r, hcode⟩ := (S.relationArity_eq_succ_iff _ _).mp hn
    exact ⟨n, r, by omega, by omega⟩
  · rintro ⟨n, r, ht, hb⟩
    simp [ht, hb, S.relationArity_code]

/-- The eight semantic components carried by the fold's grammar fields. -/
structure Sound (A : LTerm) : Prop where
  term : termBit (state S A) = 1 → ∃ t : L.Term ℕ, A.Alpha (S.encodeTerm t)
  args : ∀ n, argsLenPlus1 (state S A) = n + 1 →
    ∃ ts : Fin n → L.Term ℕ, A.Alpha (encodeVector (fun i => S.encodeTerm (ts i)))
  functionPayload : functionPayloadBit (state S A) = 1 →
    ∃ (n : ℕ) (f : L.Functions n) (ts : Fin n → L.Term ℕ),
      A.Alpha (.app (tag (S.functionCode ⟨n, f⟩)) (encodeVector (fun i => S.encodeTerm (ts i))))
  relationPayload : relationPayloadBit (state S A) = 1 →
    ∃ (n : ℕ) (r : L.Relations n) (ts : Fin n → L.Term ℕ),
      A.Alpha (.app (tag (S.relationCode ⟨n, r⟩)) (encodeVector (fun i => S.encodeTerm (ts i))))
  termPair : termPairBit (state S A) = 1 →
    ∃ t r : L.Term ℕ, A.Alpha (.app (S.encodeTerm t) (S.encodeTerm r))
  formula : formulaBit (state S A) = 1 → ∃ φ : Formula L, A.Alpha (S.encodeFormula φ)
  binaryFormula : binaryFormulaBit (state S A) = 1 →
    ∃ φ ψ : Formula L, A.Alpha (.app (S.encodeFormula φ) (S.encodeFormula ψ))
  quantifiedFormula : quantFormulaBit (state S A) = 1 →
    ∃ (x : ℕ) (φ : Formula L), A.Alpha (.lam x (S.encodeFormula φ))

private theorem product_one {a b : ℕ} (h : a * b = 1) : a = 1 ∧ b = 1 :=
  ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩

private theorem state_sound_of_tags
    (htags : ∀ A n, tagIndexPlus1 (state S A) = n + 1 ↔ A.Alpha (tag n))
    (A : LTerm) : Sound S A := by
  induction A with
  | var x =>
    refine ⟨fun _ => ⟨.var x, .refl _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [state]
  | lam x A ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [state]
    · intro n h
      simp only [state, argsLenPlus1_pack] at h
      split_ifs at h with ht
      · have hn : n = 0 := by omega
        subst n
        exact ⟨Fin.elim0, (htags (.lam x A) 9).mp (by simpa only [state, tagIndexPlus1_pack] using ht)⟩
    · simp [state]
    · simp [state]
    · simp [state]
    · simp [state]
    · simp [state]
    · intro h
      obtain ⟨φ, hφ⟩ := ih.formula (by simpa only [state, quantFormulaBit_pack] using h)
      exact ⟨x, φ, hφ.lam x⟩
  | app A B ihA ihB =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      simp only [state, termBit_pack] at h
      split_ifs at h with ht
      · obtain ⟨n, f, ts, hp⟩ := ihB.functionPayload h
        exact ⟨.func f ts, ((htags A 8).mp ht).app hp⟩
    · intro n h
      simp only [state, argsLenPlus1_pack] at h
      split_ifs at h with ha hb
      · have ha1 : termBit (state S A) = 1 := by have := (state_bits S A).1; omega
        obtain ⟨t, ht⟩ := ihA.term ha1
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hb
        have hn : n = m + 1 := by omega
        subst n
        obtain ⟨ts, hts⟩ := ihB.args m hm
        refine ⟨Fin.cons t ts, ?_⟩
        simpa only [encodeVector, Fin.cons_zero, Fin.cons_succ] using ht.app hts
    · intro h
      obtain ⟨n, f, ht, hs⟩ := (function_payload_iff S _ _).mp
        (by simpa only [state, functionPayloadBit_pack] using h)
      obtain ⟨ts, hts⟩ := ihB.args n hs
      exact ⟨n, f, ts, ((htags A _).mp ht).app hts⟩
    · intro h
      obtain ⟨n, r, ht, hs⟩ := (relation_payload_iff S _ _).mp
        (by simpa only [state, relationPayloadBit_pack] using h)
      obtain ⟨ts, hts⟩ := ihB.args n hs
      exact ⟨n, r, ts, ((htags A _).mp ht).app hts⟩
    · intro h
      have hh : termBit (state S A) = 1 ∧ termBit (state S B) = 1 :=
        product_one (by simpa only [state, termPairBit_pack] using h)
      obtain ⟨t, ht⟩ := ihA.term hh.1
      obtain ⟨r, hr⟩ := ihB.term hh.2
      exact ⟨t, r, ht.app hr⟩
    · intro h
      simp only [state, formulaBit_pack, appFormula] at h
      split_ifs at h with h0 hp h1 h2 h3 h4 h5 h6 h7
      · exact ⟨.falsum, ((htags A 0).mp h0).app ((htags B 0).mp hp)⟩
      · obtain ⟨t, r, hr⟩ := ihB.termPair h
        exact ⟨.equal t r, ((htags A 1).mp h1).app hr⟩
      · obtain ⟨n, r, ts, hr⟩ := ihB.relationPayload h
        exact ⟨.rel r ts, ((htags A 2).mp h2).app hr⟩
      · obtain ⟨φ, ψ, hh⟩ := ihB.binaryFormula h
        exact ⟨.binary .conj φ ψ, ((htags A 3).mp h3).app hh⟩
      · obtain ⟨φ, ψ, hh⟩ := ihB.binaryFormula h
        exact ⟨.binary .disj φ ψ, ((htags A 4).mp h4).app hh⟩
      · obtain ⟨φ, ψ, hh⟩ := ihB.binaryFormula h
        exact ⟨.binary .imp φ ψ, ((htags A 5).mp h5).app hh⟩
      · obtain ⟨x, φ, hh⟩ := ihB.quantifiedFormula h
        exact ⟨.quant .all x φ, ((htags A 6).mp h6).app hh⟩
      · obtain ⟨x, φ, hh⟩ := ihB.quantifiedFormula h
        exact ⟨.quant .ex x φ, ((htags A 7).mp h7).app hh⟩
    · intro h
      have hh : formulaBit (state S A) = 1 ∧ formulaBit (state S B) = 1 :=
        product_one (by simpa only [state, binaryFormulaBit_pack] using h)
      obtain ⟨φ, hφ⟩ := ihA.formula hh.1
      obtain ⟨ψ, hψ⟩ := ihB.formula hh.2
      exact ⟨φ, ψ, hφ.app hψ⟩
    · simp [state]

private theorem args_complete_of_tags
    (htags : ∀ A n, tagIndexPlus1 (state S A) = n + 1 ↔ A.Alpha (tag n))
    {n : ℕ} (ts : Fin n → L.Term ℕ)
    (ht : ∀ i (R : ℕ → ℕ → Prop) (A : LTerm),
      Term.NameRel R A (S.encodeTerm (ts i)) → termBit (state S A) = 1) :
    ∀ (R : ℕ → ℕ → Prop) (A : LTerm),
      Term.NameRel R A (encodeVector (fun i => S.encodeTerm (ts i))) →
        argsLenPlus1 (state S A) = n + 1 := by
  induction n with
  | zero =>
    intro R A h
    have hh := (htags A 9).mpr (FirstOrderLambdaEncoding.source_tag_alpha h)
    cases A <;> simp only [state, tagIndexPlus1_pack] at hh
    · contradiction
    · contradiction
    · simp only [state, argsLenPlus1_pack, hh, ite_true]
  | succ n ih =>
    intro R A h
    cases h with
    | app ha hb =>
      have hterm := ht 0 _ _ ha
      have hargs := ih (fun i => ts i.succ) (fun i => ht i.succ) _ _ hb
      simp [state, hterm, hargs]

private theorem term_complete_of_tags
    (htags : ∀ A n, tagIndexPlus1 (state S A) = n + 1 ↔ A.Alpha (tag n))
    (t : L.Term ℕ) : ∀ (R : ℕ → ℕ → Prop) (A : LTerm),
      Term.NameRel R A (S.encodeTerm t) → termBit (state S A) = 1 := by
  induction t with
  | var x => intro R A h; cases h; simp [state]
  | func f ts ih =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ 8).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      cases hp with
      | app hs ha =>
        have hs' := (htags _ _).mpr (FirstOrderLambdaEncoding.source_tag_alpha hs)
        have ha' := args_complete_of_tags S htags ts ih _ _ ha
        simp [state, hk', symbolPayload, hs', ha', S.functionArity_code]

private theorem formula_complete_of_tags
    (htags : ∀ A n, tagIndexPlus1 (state S A) = n + 1 ↔ A.Alpha (tag n))
    (φ : Formula L) : ∀ (R : ℕ → ℕ → Prop) (A : LTerm),
      Term.NameRel R A (S.encodeFormula φ) → formulaBit (state S A) = 1 := by
  induction φ with
  | falsum =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ 0).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      have hp' := (htags _ 0).mpr (FirstOrderLambdaEncoding.source_tag_alpha hp)
      simp [state, appFormula, hk', hp']
  | equal t r =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ 1).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      cases hp with
      | app ht hr =>
        have ht' := term_complete_of_tags S htags t _ _ ht
        have hr' := term_complete_of_tags S htags r _ _ hr
        simp [state, appFormula, hk', ht', hr']
  | rel r ts =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ 2).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      cases hp with
      | app hs ha =>
        have hs' := (htags _ _).mpr (FirstOrderLambdaEncoding.source_tag_alpha hs)
        have ha' := args_complete_of_tags S htags ts (fun i => term_complete_of_tags S htags (ts i)) _ _ ha
        simp [state, appFormula, hk', symbolPayload, hs', ha', S.relationArity_code]
  | binary c φ ψ ihφ ihψ =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ (connectiveCode c)).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      cases hp with
      | app hφ hψ =>
        have hφ' := ihφ _ _ hφ
        have hψ' := ihψ _ _ hψ
        cases c <;> simp [state, appFormula, connectiveCode, hφ', hψ'] at hk' ⊢ <;>
          simp [hk']
  | quant q x φ ih =>
    intro R A h
    cases h with
    | app hk hp =>
      have hk' := (htags _ (quantifierCode q)).mpr (FirstOrderLambdaEncoding.source_tag_alpha hk)
      cases hp with
      | lam hφ =>
        have hφ' := ih _ _ hφ
        cases q <;> simp [state, appFormula, quantifierCode, hφ'] at hk' ⊢ <;>
          simp [hk']

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Compare tags
    structurally up to $\alpha$-equivalence. The given symbol programs check arities, including zero, so a structural
    syntax fold recognizes exactly the term and formula data.
-/
/-- No grammar premise remains: the tag test is the proved concrete fold. -/
theorem state_sound (A : LTerm) : Sound S A :=
  state_sound_of_tags S (tagIndexPlus1_eq_succ_iff S) A

theorem termBit_of_nameRel (t : L.Term ℕ) (R : ℕ → ℕ → Prop) (A : LTerm)
    (h : Term.NameRel R A (S.encodeTerm t)) : termBit (state S A) = 1 :=
  term_complete_of_tags S (tagIndexPlus1_eq_succ_iff S) t R A h

theorem formulaBit_of_nameRel (φ : Formula L) (R : ℕ → ℕ → Prop) (A : LTerm)
    (h : Term.NameRel R A (S.encodeFormula φ)) : formulaBit (state S A) = 1 :=
  formula_complete_of_tags S (tagIndexPlus1_eq_succ_iff S) φ R A h

theorem termBit_iff (A : LTerm) : termBit (state S A) = 1 ↔
    ∃ t : L.Term ℕ, A.Alpha (S.encodeTerm t) := by
  refine ⟨(state_sound S A).term, ?_⟩
  rintro ⟨t, ht⟩
  exact term_complete_of_tags S (tagIndexPlus1_eq_succ_iff S) t Eq A
    ((Term.renameEq_iff_nameRel _ _).mp ht)

theorem formulaBit_iff (A : LTerm) : formulaBit (state S A) = 1 ↔
    ∃ φ : Formula L, A.Alpha (S.encodeFormula φ) := by
  refine ⟨(state_sound S A).formula, ?_⟩
  rintro ⟨φ, hφ⟩
  exact formula_complete_of_tags S (tagIndexPlus1_eq_succ_iff S) φ Eq A
    ((Term.renameEq_iff_nameRel _ _).mp hφ)

def IsTermCode (n : ℕ) : Prop := ∃ t : L.Term ℕ, (Term.decode n).Alpha (S.encodeTerm t)
def IsFormulaCode (n : ℕ) : Prop := ∃ φ : Formula L, (Term.decode n).Alpha (S.encodeFormula φ)

/-- Decidability is obtained from the computed flag and its correspondence
proof, without an assumed parser or an assumed local-rule decision procedure. -/
instance termCodeDecidable (n : ℕ) : Decidable (IsTermCode S n) :=
  decidable_of_iff (termBit (state S (Term.decode n)) = 1) (termBit_iff S _)
instance formulaCodeDecidable (n : ℕ) : Decidable (IsFormulaCode S n) :=
  decidable_of_iff (formulaBit (state S (Term.decode n)) = 1) (formulaBit_iff S _)

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
