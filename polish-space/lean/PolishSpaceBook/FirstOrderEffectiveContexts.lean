module

public import PolishSpaceBook.FirstOrderEffectiveSyntax
public import PolishSpaceBook.FirstOrderLambdaContextClasses

@[expose] public section

/-! # Finite contexts over a general effective signature

Raw lists represent finite sets of encoded alpha-classes. The representation
relation is defined by the concrete encoding; it is not a checker specification.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable local instance effectiveFormulaClassDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
noncomputable local instance effectiveSyntaxClassDecidableEq : DecidableEq AlphaTerm := Classical.decEq _

def encodeClass : AlphaFormula L → AlphaTerm :=
  Quotient.map S.encodeFormula (fun φ ψ h => (S.encodeFormula_alpha_iff φ ψ).mpr h)

@[simp] theorem encodeClass_mk (φ : Formula L) : S.encodeClass (AlphaFormula.mk φ) = AlphaTerm.mk (S.encodeFormula φ) := rfl

theorem encodeClass_injective : Function.Injective S.encodeClass := by
  intro A B
  induction A using Quotient.inductionOn with
  | _ φ =>
    induction B using Quotient.inductionOn with
    | _ ψ =>
      intro h
      exact (AlphaFormula.mk_eq_iff φ ψ).mpr
        ((S.encodeFormula_alpha_iff φ ψ).mp ((AlphaTerm.mk_eq_iff _ _).mp h))

def FormulaRep (n : ℕ) (A : AlphaFormula L) : Prop := AlphaTerm.mk (Term.decode n) = S.encodeClass A

def ContextRep (e : ℕ) (Γ : Context L) : Prop := ContextPrograms.rawContext e = Γ.image S.encodeClass

theorem formulaRep_mk_iff (n : ℕ) (φ : Formula L) :
    S.FormulaRep n (AlphaFormula.mk φ) ↔ (Term.decode n).Alpha (S.encodeFormula φ) :=
  AlphaTerm.mk_eq_iff _ _

theorem formulaRep_encode (φ : Formula L) : S.FormulaRep (S.encodeFormula φ).code (AlphaFormula.mk φ) := by
  simp only [FormulaRep, Term.decode_code, encodeClass_mk]

theorem formulaRep_unique {a : ℕ} {A B : AlphaFormula L} (ha : S.FormulaRep a A) (hb : S.FormulaRep a B) : A = B :=
  S.encodeClass_injective (ha.symm.trans hb)

theorem formulaRep_alpha_iff {a b : ℕ} {A B : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) :
    (Term.decode a).Alpha (Term.decode b) ↔ A = B := by
  rw [← AlphaTerm.mk_eq_iff, ha, hb]
  exact S.encodeClass_injective.eq_iff

theorem formulaRep_fv {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A) :
    (Term.decode a).fv = A.fv := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    change (Term.decode a).fv = φ.fv
    simpa only [S.encodeFormula_fv] using ((S.formulaRep_mk_iff a φ).mp ha).fv_eq

theorem formulaRep_exists_iff (a : ℕ) :
    (∃ A : AlphaFormula L, S.FormulaRep a A) ↔ ∃ φ : Formula L, (Term.decode a).Alpha (S.encodeFormula φ) := by
  constructor
  · rintro ⟨A, hA⟩
    induction A using Quotient.inductionOn with
    | _ φ => exact ⟨φ, (S.formulaRep_mk_iff a φ).mp hA⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨AlphaFormula.mk φ, (S.formulaRep_mk_iff a φ).mpr hφ⟩

theorem contextRep_equal {e d : ℕ} {Γ Δ : Context L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) :
    ContextPrograms.equalBit e d = true ↔ Γ = Δ := by
  rw [ContextPrograms.equalBit_iff, he, hd]
  exact ⟨fun h => Finset.image_injective S.encodeClass_injective h, congrArg (Finset.image S.encodeClass)⟩

theorem contextRep_member {a e : ℕ} {A : AlphaFormula L} {Γ : Context L}
    (ha : S.FormulaRep a A) (he : S.ContextRep e Γ) :
    ContextPrograms.member a e = true ↔ A ∈ Γ := by
  rw [ContextPrograms.member_rawContext, he, ha, Finset.mem_image]
  exact ⟨fun ⟨B, hB, hBA⟩ => S.encodeClass_injective hBA ▸ hB, fun hA => ⟨A, hA, rfl⟩⟩

theorem contextRep_empty : S.ContextRep 0 (∅ : Context L) := by
  simp [ContextRep, ContextPrograms.rawContext, NatListCode.decode]

theorem contextRep_insert {a e : ℕ} {A : AlphaFormula L} {Γ : Context L}
    (ha : S.FormulaRep a A) (he : S.ContextRep e Γ) :
    S.ContextRep (Nat.pair a e + 1) (insert A Γ) := by
  change ContextPrograms.rawContext _ = _
  rw [ContextPrograms.rawContext_cons, ha, he, Finset.image_insert]

theorem contextRep_exists_iff (e : ℕ) :
    (∃ Γ : Context L, S.ContextRep e Γ) ↔
      ∀ a ∈ NatListCode.decode e, ∃ A : AlphaFormula L, S.FormulaRep a A := by
  constructor
  · rintro ⟨Γ, hΓ⟩ a ha
    have hm : AlphaTerm.mk (Term.decode a) ∈ ContextPrograms.rawContext e :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [hΓ, Finset.mem_image] at hm
    obtain ⟨A, _, hA⟩ := hm
    exact ⟨A, hA.symm⟩
  · intro h
    have aux : ∀ (xs : List ℕ), (∀ a ∈ xs, ∃ A : AlphaFormula L, S.FormulaRep a A) →
        ∃ Γ : Context L, S.ContextRep (NatListCode.encode xs) Γ := by
      intro xs
      induction xs with
      | nil => intro _; exact ⟨∅, S.contextRep_empty⟩
      | cons a xs ih =>
        intro hh
        obtain ⟨A, hA⟩ := hh a (by simp)
        obtain ⟨Γ, hΓ⟩ := ih (fun b hb => hh b (by simp [hb]))
        exact ⟨insert A Γ, S.contextRep_insert hA hΓ⟩
    simpa only [NatListCode.encode_decode] using aux (NatListCode.decode e) h

theorem context_has_code (Γ : Context L) : ∃ e : ℕ, S.ContextRep e Γ := by
  induction Γ using Finset.induction_on with
  | empty => exact ⟨0, S.contextRep_empty⟩
  | @insert A Γ _ ih =>
    obtain ⟨e, he⟩ := ih
    induction A using Quotient.inductionOn with
    | _ φ => exact ⟨Nat.pair (S.encodeFormula φ).code e + 1,
        S.contextRep_insert (S.formulaRep_encode φ) he⟩

theorem contextRep_free {e : ℕ} {Γ : Context L} (he : S.ContextRep e Γ) (x : ℕ) :
    ContextPrograms.hasFree x e = true ↔ x ∈ Γ.fv := by
  simp only [ContextPrograms.hasFree, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨A, hA⟩ := (S.contextRep_exists_iff e).mp ⟨Γ, he⟩ a ha
    have hm : A ∈ Γ := (S.contextRep_member hA he).mp
      ((ContextPrograms.member_rawContext a e).mpr
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)))
    exact Finset.mem_biUnion.mpr ⟨A, hm, by rwa [← S.formulaRep_fv hA]⟩
  · intro hx
    obtain ⟨A, hAΓ, hx⟩ := Finset.mem_biUnion.mp hx
    have hm : S.encodeClass A ∈ ContextPrograms.rawContext e := by
      rw [he]; exact Finset.mem_image.mpr ⟨A, hAΓ, rfl⟩
    obtain ⟨a, ha, hAa⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact ⟨a, ha, by rwa [S.formulaRep_fv hAa]⟩

theorem formulaRep_substitute {a r : ℕ} {A : AlphaFormula L} {t : L.Term ℕ}
    (ha : S.FormulaRep a A) (hr : (Term.decode r).Alpha (S.encodeTerm t)) (x : ℕ) :
    S.FormulaRep ((Term.decode a).subst x (Term.decode r)).code (A.subst x t) := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    apply (S.formulaRep_mk_iff _ _).mpr
    rw [Term.decode_code]
    exact (((S.formulaRep_mk_iff a φ).mp ha).subst hr x).trans (S.encodeFormula_subst_alpha φ x t)

theorem contextRep_substitution {e d a r : ℕ} {Γ Δ : Context L} {A : AlphaFormula L} {t : L.Term ℕ}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A)
    (hr : (Term.decode r).Alpha (S.encodeTerm t)) (x : ℕ) :
    ContextPrograms.equalBit d (Nat.pair ((Term.decode a).subst x (Term.decode r)).code e + 1) = true ↔
      Δ = insert (A.subst x t) Γ :=
  S.contextRep_equal hd (S.contextRep_insert (S.formulaRep_substitute ha hr x) he)

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
