module

public import PolishSpaceBook.FirstOrderLocalSequentInterpretation

@[expose] public section

/-! # Bounded quantifier witnesses on arbitrary accepted raw codes

The numerical bounds depend on the supplied codes, not on a canonical re-encoding.
Free names in the parsed formulas are bounded directly by those raw codes.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedFirstOrder FirstOrder Language
open LocalRulePrograms ContextPrograms
noncomputable local instance rawFormulaDecidableEq : DecidableEq (AlphaFormula ForcingFormulas.membershipLanguage) := Classical.decEq _
noncomputable local instance rawTermDecidableEq : DecidableEq NamedLambda.AlphaTerm := Classical.decEq _

theorem fv_subset_syntaxNames (t : LTerm) : t.fv ⊆ EqualityMatcher.syntaxNames t := by
  induction t with
  | var x => simp [Term.fv, EqualityMatcher.syntaxNames]
  | app a b ha hb =>
    simpa only [Term.fv, EqualityMatcher.syntaxNames] using Finset.union_subset_union ha hb
  | lam x a ha =>
    intro y hy
    exact Finset.mem_insert_of_mem (ha (Finset.mem_erase.mp hy).2)

theorem raw_freeName_le_code (t : LTerm) {x : ℕ} (hx : x ∈ t.fv) : x ≤ t.code :=
  EqualityMatcher.syntaxName_le_code t (fv_subset_syntaxNames t hx)

theorem parsed_freeName_le_code {a : ℕ} {φ : FOL} (ha : parseCode a = some φ)
    {x : ℕ} (hx : x ∈ φ.fv) : x ≤ a := by
  have h := raw_freeName_le_code (Term.decode a) (by rwa [parseCode_fv ha])
  simpa only [Term.code_decode] using h

theorem parsed_context_name_bound {e : ℕ} {Γ : List FOL} (he : parseContext e = some Γ)
    {x : ℕ} (hx : x ∈ (context Γ).fv) : x ≤ e := by
  have h := (parseContext_free he x).mpr hx
  simp only [hasFree, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨a, ha, hx⟩ := h
  have hxa := raw_freeName_le_code (Term.decode a) hx
  have hae := member_le_listCode ha
  simp only [Term.code_decode] at hxa
  simp only [NatListCode.encode_decode] at hae
  exact hxa.trans hae

theorem parsed_substitute_alpha {a : ℕ} {φ : FOL} (ha : parseCode a = some φ) (x t : ℕ) :
    ((Term.decode a).subst x (.var t)).Alpha (encode (φ.subst x (.var t))) :=
  ((parse_sound _ _ ha).subst (.refl _) x).trans (encode_subst_alpha φ x t)

theorem raw_instance_iff {a b : ℕ} {φ ψ : FOL}
    (ha : parseCode a = some φ) (hb : parseCode b = some ψ) (x t : ℕ) :
    ((Term.decode a).subst x (.var t)).Alpha (Term.decode b) ↔ (φ.subst x (.var t)).Alpha ψ := by
  rw [← encode_alpha_iff]
  have hs := parsed_substitute_alpha ha x t
  have ht := parse_sound _ _ hb
  exact ⟨fun h => hs.symm.trans (h.trans ht), fun h => hs.trans (h.trans ht.symm)⟩

theorem raw_instance_witness_bounded {b : ℕ} {ψ : FOL} (hb : parseCode b = some ψ)
    (φ : FOL) (x : ℕ) :
    (∃ t, (φ.subst x (.var t)).Alpha ψ) ↔ ∃ t < b + 1, (φ.subst x (.var t)).Alpha ψ := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases hx : x ∈ φ.fv
    · have hfv : t ∈ ψ.fv := by
        rw [← ht.fv_eq, Formula.mem_fv_subst]
        exact Or.inr ⟨hx, by simp⟩
      exact ⟨t, Nat.lt_succ_of_le (parsed_freeName_le_code hb hfv), ht⟩
    · exact ⟨0, by omega, (absent_instance_alpha φ x 0 hx).trans
        ((absent_instance_alpha φ x t hx).symm.trans ht)⟩
  · rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩

theorem raw_instanceSearch_iff {a b : ℕ} {φ ψ : FOL}
    (ha : parseCode a = some φ) (hb : parseCode b = some ψ) (x : ℕ) :
    InstancePrograms.searchValue (InstancePrograms.input a x b) ≠ 0 ↔
      ∃ t, (φ.subst x (.var t)).Alpha ψ := by
  rw [InstancePrograms.searchValue_ne_zero]
  simp only [InstancePrograms.input, Nat.unpair_pair, InstancePrograms.test, raw_instance_iff ha hb]
  exact (raw_instance_witness_bounded hb φ x).symm

theorem raw_quant_alpha {a : ℕ} {φ : FOL} (ha : parseCode a = some φ)
    (q : Quantifier) (x : ℕ) :
    (node (quantifierCode q) (.lam x (Term.decode a))).Alpha (encode (.quant q x φ)) :=
  (Term.Alpha.refl _).app ((parse_sound _ _ ha).lam x)

theorem raw_allTest_iff {e a b : ℕ} {Γ : List FOL} {φ ψ : FOL}
    (he : parseContext e = some Γ) (ha : parseCode a = some φ) (hb : parseCode b = some ψ) (x : ℕ) :
    EigenvariablePrograms.allTest.value (Nat.pair (EigenvariablePrograms.allInput e a b) x) ≠ 0 ↔
      allIntroWitness Γ φ ψ x := by
  simp only [EigenvariablePrograms.allTest, Grammar.Program.mul, EigenvariablePrograms.Program.isZero,
    Grammar.Program.ifZero, Grammar.Program.const, EigenvariablePrograms.Program.contextFree,
    TemplatePrograms.Program.binary, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, id_eq, EigenvariablePrograms.allInput, Nat.unpair_pair,
    Grammar.Program.alpha, EigenvariablePrograms.Program.quant_value, Term.decode_code]
  have hq : (node 6 (.lam x (Term.decode a))).Alpha (Term.decode b) ↔
      (Formula.quant .all x φ).Alpha ψ := by
    rw [← encode_alpha_iff]
    have hα := raw_quant_alpha ha .all x
    have hβ := parse_sound _ _ hb
    exact ⟨fun h => hα.symm.trans (h.trans hβ), fun h => hα.trans (h.trans hβ.symm)⟩
  simp only [parseContext_free he, hq, allIntroWitness]
  by_cases hc : x ∈ (context Γ).fv <;>
    by_cases h : (Formula.quant .all x φ).Alpha ψ <;> simp [hc, h]

theorem raw_allSearch_iff {e a b : ℕ} {Γ : List FOL} {φ ψ : FOL}
    (he : parseContext e = some Γ) (ha : parseCode a = some φ) (hb : parseCode b = some ψ) :
    EigenvariablePrograms.allSearchValue (EigenvariablePrograms.allInput e a b) ≠ 0 ↔
      ∃ x, allIntroWitness Γ φ ψ x := by
  rw [EigenvariablePrograms.allSearchValue, NamedLambda.AlphaTerm.boundedAnyBit_ne_zero]
  have hbound : (EigenvariablePrograms.allInput e a b).unpair.1 +
      (EigenvariablePrograms.allInput e a b).unpair.2.unpair.1 + 2 = e + a + 2 := by
    simp only [EigenvariablePrograms.allInput, Nat.unpair_pair]
  rw [hbound]
  simp only [raw_allTest_iff he ha hb]
  constructor
  · rintro ⟨x, _, hx⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hxΓ, hxψ⟩
    by_cases hx : x ∈ φ.fv
    · exact ⟨x, by have := parsed_freeName_le_code ha hx; omega, hxΓ, hxψ⟩
    · let z := e + a + 1
      have hzΓ : z ∉ (context Γ).fv := by
        intro h; have := parsed_context_name_bound he h; dsimp [z] at *; omega
      have hzφ : z ∉ φ.fv := by
        intro h; have := parsed_freeName_le_code ha h; dsimp [z] at *; omega
      exact ⟨z, by dsimp [z]; omega, hzΓ, (quant_absent_alpha .all φ z x hzφ hx).trans hxψ⟩

theorem raw_context_substitution_iff {e d a : ℕ} {Γ Δ : List FOL} {φ : FOL}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ) (ha : parseCode a = some φ)
    (x y : ℕ) :
    equalBit d (Nat.pair ((Term.decode a).subst x (.var y)).code e + 1) = true ↔
      context Δ = insert (AlphaFormula.mk (φ.subst x (.var y))) (context Γ) := by
  rw [equalBit_iff, rawContext_cons, parseContext_raw he, parseContext_raw hd, Term.decode_code]
  have hs : NamedLambda.AlphaTerm.mk ((Term.decode a).subst x (.var y)) =
      encodeClass (AlphaFormula.mk (φ.subst x (.var y))) :=
    (NamedLambda.AlphaTerm.mk_eq_iff _ _).mpr (parsed_substitute_alpha ha x y)
  rw [hs, ← Finset.image_insert]
  exact ⟨fun h => Finset.image_injective encodeClass_injective h, congrArg (Finset.image encodeClass)⟩

theorem raw_quant_fv {a : ℕ} {φ : FOL} (ha : parseCode a = some φ)
    (q : Quantifier) (x : ℕ) :
    (node (quantifierCode q) (.lam x (Term.decode a))).fv = (Formula.quant q x φ).fv := by
  simpa only [encode_fv] using (raw_quant_alpha ha q x).fv_eq

theorem raw_exTest_iff {e d a b : ℕ} {Γ Δ : List FOL} {φ χ : FOL}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ)
    (ha : parseCode a = some φ) (hb : parseCode b = some χ) (x y : ℕ) :
    EigenvariablePrograms.exTest.value (Nat.pair (EigenvariablePrograms.exInput e d a b x) y) ≠ 0 ↔
      exElimWitness Γ Δ φ χ x y := by
  simp only [EigenvariablePrograms.exTest, Grammar.Program.mul, EigenvariablePrograms.Program.isZero,
    Grammar.Program.ifZero, Grammar.Program.const, EigenvariablePrograms.Program.contextFree,
    EigenvariablePrograms.Program.formulaFree, EigenvariablePrograms.Program.contextEqual,
    EigenvariablePrograms.Program.substitute, TemplatePrograms.Program.binary, TemplatePrograms.Program.cons,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq,
    EigenvariablePrograms.exInput, Nat.unpair_pair, EigenvariablePrograms.Program.quant_value, Term.decode_code]
  have hf := raw_quant_fv ha .ex x
  change (node 7 (.lam x (Term.decode a))).fv = (Formula.quant .ex x φ).fv at hf
  simp only [raw_context_substitution_iff he hd ha, parseContext_free he, parseCode_fv hb,
    hf, exElimWitness, Finset.mem_union, not_or]
  by_cases hc : context Δ = insert (AlphaFormula.mk (φ.subst x (.var y))) (context Γ) <;>
    by_cases hΓ : y ∈ (context Γ).fv <;> by_cases hχ : y ∈ χ.fv <;>
    by_cases hφ : y ∈ (Formula.quant .ex x φ).fv <;> simp [hc, hΓ, hχ, hφ]

theorem raw_exBound_value (e d a b x : ℕ) :
    EigenvariablePrograms.exBound.value (EigenvariablePrograms.exInput e d a b x) =
      e + d + b + (node 7 (.lam x (Term.decode a))).code + 2 := by
  simp only [EigenvariablePrograms.exBound, EigenvariablePrograms.Program.add,
    EigenvariablePrograms.Program.quant_value, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, Grammar.Program.const, id_eq, EigenvariablePrograms.exInput, Nat.unpair_pair]

theorem raw_exSearch_iff {e d a b : ℕ} {Γ Δ : List FOL} {φ χ : FOL}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ)
    (ha : parseCode a = some φ) (hb : parseCode b = some χ) (x : ℕ) :
    EigenvariablePrograms.exSearchValue (EigenvariablePrograms.exInput e d a b x) ≠ 0 ↔
      ∃ y, exElimWitness Γ Δ φ χ x y := by
  rw [EigenvariablePrograms.exSearchValue, NamedLambda.AlphaTerm.boundedAnyBit_ne_zero]
  simp only [raw_exTest_iff he hd ha hb, raw_exBound_value]
  constructor
  · rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, hΔ, hy⟩
    by_cases hx : x ∈ φ.fv
    · have hfv : y ∈ (context Δ).fv := by
        apply Finset.mem_biUnion.mpr
        refine ⟨AlphaFormula.mk (φ.subst x (.var y)), ?_, ?_⟩
        · rw [hΔ]; simp
        · change y ∈ (φ.subst x (.var y)).fv
          rw [Formula.mem_fv_subst]
          exact Or.inr ⟨hx, by simp⟩
      exact ⟨y, by have := parsed_context_name_bound hd hfv; omega, hΔ, hy⟩
    · let c := (node 7 (.lam x (Term.decode a))).code
      let z := e + b + c + 1
      have hzΓ : z ∉ (context Γ).fv := by
        intro h; have := parsed_context_name_bound he h; dsimp [z] at *; omega
      have hzχ : z ∉ χ.fv := by
        intro h; have := parsed_freeName_le_code hb h; dsimp [z] at *; omega
      have hzφ : z ∉ (Formula.quant .ex x φ).fv := by
        intro h
        have hf := raw_quant_fv ha .ex x
        change (node 7 (.lam x (Term.decode a))).fv = (Formula.quant .ex x φ).fv at hf
        have ht := raw_freeName_le_code (node 7 (.lam x (Term.decode a))) (hf.symm ▸ h)
        change z ≤ c at ht
        dsimp [z] at ht
        omega
      have hsame : AlphaFormula.mk (φ.subst x (.var y)) = AlphaFormula.mk (φ.subst x (.var z)) :=
        (AlphaFormula.mk_eq_iff _ _).mpr
          ((absent_instance_alpha φ x y hx).trans (absent_instance_alpha φ x z hx).symm)
      refine ⟨z, by dsimp [z, c]; omega, ?_, ?_⟩
      · exact hΔ.trans (congrArg (fun α => insert α (context Γ)) hsame)
      · simpa only [Finset.mem_union, not_or] using And.intro (And.intro hzΓ hzχ) hzφ

end PolishSpaceBook.FirstOrderLambdaEncoding
