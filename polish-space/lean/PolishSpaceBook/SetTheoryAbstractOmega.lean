module

public import PolishSpaceBook.SetTheoryInternalInduction

@[expose] public section

/-! # The least inductive set in arbitrary membership models

Infinity and Separation construct the internal natural-number object. Its
induction principle applies to actual formulas, including all parameters;
it does not identify a possibly nonstandard model's naturals with `ℕ`.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def IsEmptyObject (e : M) : Prop := ∀ z : M, ¬member z e

def IsSuccessorObject (a b : M) : Prop :=
  ∀ z : M, member z b ↔ member z a ∨ z = a

def IsInductiveObject (I : M) : Prop :=
  (∃ e : M, member e I ∧ IsEmptyObject e) ∧
    ∀ a : M, member a I → ∃ b : M, member b I ∧ IsSuccessorObject a b

def IsLeastInductiveObject (W : M) : Prop :=
  IsInductiveObject W ∧ ∀ I : M, IsInductiveObject I → ∀ a : M, member a W → member a I

def emptyObjectBody : ForcingFormulas.Formula 1 := (memberAt (1 : Fin 2) 0).not.all

def successorObjectBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 1).iff (memberAt 2 0 ⊔ equalAt 2 0)).all

theorem realize_emptyObjectBody (xs : Fin 1 → M) :
    emptyObjectBody.Realize Empty.elim xs ↔ IsEmptyObject (xs 0) := by
  simp [emptyObjectBody, IsEmptyObject, BoundedFormula.realize_all,
    BoundedFormula.realize_not, realize_memberAt, Fin.snoc]

theorem realize_successorObjectBody (xs : Fin 2 → M) :
    successorObjectBody.Realize Empty.elim xs ↔ IsSuccessorObject (xs 0) (xs 1) := by
  simp [successorObjectBody, IsSuccessorObject, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_sup, realize_memberAt, realize_equalAt, Fin.snoc]

def inductiveObjectBody : ForcingFormulas.Formula 1 :=
  ((memberAt (1 : Fin 2) 0 ⊓ (memberAt (2 : Fin 3) 1).not.all).ex) ⊓
    (((memberAt (1 : Fin 2) 0).imp
      ((memberAt (2 : Fin 3) 0 ⊓
        ((memberAt (3 : Fin 4) 2).iff (memberAt 3 1 ⊔ equalAt 3 1)).all).ex)).all)

theorem realize_inductiveObjectBody (xs : Fin 1 → M) :
    inductiveObjectBody.Realize Empty.elim xs ↔ IsInductiveObject (xs 0) := by
  simp [inductiveObjectBody, IsInductiveObject, IsEmptyObject, IsSuccessorObject,
    BoundedFormula.realize_inf, BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_sup, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, realize_memberAt, realize_equalAt, Fin.snoc]

def omegaMembershipBody : ForcingFormulas.Formula 1 :=
  ((reindex inductiveObjectBody ![(1 : Fin 2)]).imp (memberAt 0 1)).all

theorem realize_omegaMembershipBody (xs : Fin 1 → M) :
    omegaMembershipBody.Realize Empty.elim xs ↔
      ∀ I : M, IsInductiveObject I → member (xs 0) I := by
  simp [omegaMembershipBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_reindex, realize_inductiveObjectBody, realize_memberAt, Fin.snoc]

theorem emptyObject_unique (hext : M ⊨ extensionalitySentence) {a b : M}
    (ha : IsEmptyObject a) (hb : IsEmptyObject b) : a = b := by
  apply (models_extensionality_iff M).mp hext a b
  intro z
  exact ⟨fun hz => False.elim (ha z hz), fun hz => False.elim (hb z hz)⟩

theorem successorObject_unique (hext : M ⊨ extensionalitySentence) {a b c : M}
    (hb : IsSuccessorObject a b) (hc : IsSuccessorObject a c) : b = c :=
  (models_extensionality_iff M).mp hext b c (fun z => (hb z).trans (hc z).symm)

theorem member_cycle_false (hp : M ⊨ pairingSentence) (hf : M ⊨ foundationSentence)
    {a b : M} (hab : member a b) (hba : member b a) : False := by
  obtain ⟨p, hpair⟩ := (models_pairing_iff M).mp hp a b
  obtain ⟨c, hcp, hc⟩ := (models_foundation_iff M).mp hf p
    ⟨a, (hpair a).mpr (Or.inl rfl)⟩
  rcases (hpair c).mp hcp with rfl | rfl
  · exact hc b hba ((hpair b).mpr (Or.inr rfl))
  · exact hc a hab ((hpair a).mpr (Or.inl rfl))

theorem successorObject_injective (hp : M ⊨ pairingSentence) (hf : M ⊨ foundationSentence)
    {a b c : M} (hac : IsSuccessorObject a c) (hbc : IsSuccessorObject b c) : a = b := by
  rcases (hbc a).mp ((hac a).mpr (Or.inr rfl)) with hab | hab
  · rcases (hac b).mp ((hbc b).mpr (Or.inr rfl)) with hba | hba
    · exact False.elim (member_cycle_false hp hf hab hba)
    · exact hba.symm
  · exact hab

/-- Separation in one Infinity witness constructs the least inductive set,
even when the model is externally ill-founded or nonstandard. -/
theorem existsUnique_leastInductiveObject (hM : M ⊨ fullZFCTheory) :
    ∃! W : M, IsLeastInductiveObject W := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  obtain ⟨I, hI⟩ := (models_infinity_iff M).mp (hM.realize_of_mem _ ZFCAxiom.infinity)
  change IsInductiveObject I at hI
  obtain ⟨W, hW⟩ := (realize_separation M omegaMembershipBody).mp
    (fullZFC_model_separation hM _) Fin.elim0 I
  have hw (a : M) : member a W ↔ member a I ∧
      ∀ J : M, IsInductiveObject J → member a J := by
    simpa only [realize_omegaMembershipBody, Fin.snoc_zero] using hW a
  have hmin : ∀ J : M, IsInductiveObject J → ∀ a : M, member a W → member a J :=
    fun J hJ a ha => ((hw a).mp ha).2 J hJ
  have hind : IsInductiveObject W := by
    constructor
    · obtain ⟨e, heI, he⟩ := hI.1
      refine ⟨e, (hw e).mpr ⟨heI, ?_⟩, he⟩
      intro J hJ
      obtain ⟨e', he'J, he'⟩ := hJ.1
      exact emptyObject_unique hext he' he ▸ he'J
    · intro a haW
      obtain ⟨b, hbI, hb⟩ := hI.2 a ((hw a).mp haW).1
      refine ⟨b, (hw b).mpr ⟨hbI, ?_⟩, hb⟩
      intro J hJ
      obtain ⟨b', hb'J, hb'⟩ := hJ.2 a (hmin J hJ a haW)
      exact successorObject_unique hext hb' hb ▸ hb'J
  refine ⟨W, ⟨hind, hmin⟩, ?_⟩
  intro V hV
  apply (models_extensionality_iff M).mp hext V W
  intro a
  exact ⟨hV.2 W hind a, hmin V hV.1 a⟩

/-- The internal natural-number induction schema is derived by Separation
and leastness; the parameter tuple is untouched. -/
theorem leastInductiveObject_induction {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hsep : M ⊨ separationSentence φ) (ps : Fin n → M) (W : M)
    (hW : IsLeastInductiveObject W)
    (hzero : ∀ e : M, member e W → IsEmptyObject e →
      φ.Realize Empty.elim (Fin.snoc ps e))
    (hsucc : ∀ a b : M, member a W → member b W → IsSuccessorObject a b →
      φ.Realize Empty.elim (Fin.snoc ps a) → φ.Realize Empty.elim (Fin.snoc ps b)) :
    ∀ a : M, member a W → φ.Realize Empty.elim (Fin.snoc ps a) := by
  obtain ⟨D, hD⟩ := (realize_separation M φ).mp hsep ps W
  have hDI : IsInductiveObject D := by
    constructor
    · obtain ⟨e, heW, he⟩ := hW.1.1
      exact ⟨e, (hD e).mpr ⟨heW, hzero e heW he⟩, he⟩
    · intro a haD
      obtain ⟨haW, haφ⟩ := (hD a).mp haD
      obtain ⟨b, hbW, hb⟩ := hW.1.2 a haW
      exact ⟨b, (hD b).mpr ⟨hbW, hsucc a b haW hbW hb haφ⟩, hb⟩
  exact fun a haW => ((hD a).mp (hW.2 D hDI a haW)).2

theorem leastInductiveObject_transitive (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) :
    ∀ a : M, member a W → ∀ b : M, member b a → member b W := by
  let φ := reindex subsetBody ![(1 : Fin 2), 0]
  have hp (a : M) : φ.Realize Empty.elim (Fin.snoc ![W] a) ↔
      ∀ b : M, member b a → member b W := by
    simp [φ, realize_reindex, subsetBody, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, realize_memberAt, Fin.snoc]
  have hi := leastInductiveObject_induction φ (fullZFC_model_separation hM _) ![W] W hW
    (fun e _ he => (hp e).mpr (fun b hb => False.elim (he b hb)))
    (fun a b haW _ hab ha => (hp b).mpr (fun c hcb => by
      rcases (hab c).mp hcb with hca | rfl
      · exact (hp a).mp ha c hca
      · exact haW))
  exact fun a ha => (hp a).mp (hi a ha)

theorem realize_transitiveFormula {n : ℕ} (i : Fin n) (xs : Fin n → M) :
    (transitiveFormula i).Realize Empty.elim xs ↔
      ∀ a : M, member a (xs i) → ∀ b : M, member b a → member b (xs i) := by
  simp only [transitiveFormula, realize_boundedAll, realize_memberAt,
    Fin.snoc_last, Fin.snoc_castSucc]

/-- Every internal natural is itself internally transitive. -/
theorem leastInductiveObject_members_transitive (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) :
    ∀ a : M, member a W → ∀ b : M, member b a → ∀ c : M, member c b → member c a := by
  let φ := transitiveFormula (0 : Fin 1)
  have hp (a : M) : φ.Realize Empty.elim (Fin.snoc Fin.elim0 a) ↔
      ∀ b : M, member b a → ∀ c : M, member c b → member c a := by
    simp only [φ, realize_transitiveFormula, Fin.snoc_zero]
  have hi := leastInductiveObject_induction φ (fullZFC_model_separation hM _) Fin.elim0 W hW
    (fun e _ he => (hp e).mpr (fun b hb => False.elim (he b hb)))
    (fun a b _ _ hab ha => (hp b).mpr (fun c hcb d hdc => by
      rcases (hab c).mp hcb with hca | rfl
      · exact (hab d).mpr (Or.inl ((hp a).mp ha c hca d hdc))
      · exact (hab d).mpr (Or.inl hdc)))
  exact fun a ha => (hp a).mp (hi a ha)

def naturalZeroOrSuccessorBody : ForcingFormulas.Formula 2 :=
  reindex emptyObjectBody ![(1 : Fin 2)] ⊔
    (memberAt (2 : Fin 3) 0 ⊓ reindex successorObjectBody ![2, 1]).ex

theorem realize_naturalZeroOrSuccessorBody (xs : Fin 2 → M) :
    naturalZeroOrSuccessorBody.Realize Empty.elim xs ↔
      IsEmptyObject (xs 1) ∨ ∃ a : M, member a (xs 0) ∧ IsSuccessorObject a (xs 1) := by
  simp [naturalZeroOrSuccessorBody, BoundedFormula.realize_sup, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, realize_reindex, realize_emptyObjectBody,
    realize_successorObjectBody, realize_memberAt, Fin.snoc]

/-- There are no internal nonzero limit naturals. This includes the model's
nonstandard naturals and is proved by its formula induction principle. -/
theorem leastInductiveObject_zero_or_successor (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) (a : M) (ha : member a W) :
    IsEmptyObject a ∨ ∃ b : M, member b W ∧ IsSuccessorObject b a := by
  have hi := leastInductiveObject_induction naturalZeroOrSuccessorBody
    (fullZFC_model_separation hM _) ![W] W hW
    (fun e _ he => (realize_naturalZeroOrSuccessorBody _).mpr (Or.inl he))
    (fun b c hb _ hbc _ => (realize_naturalZeroOrSuccessorBody _).mpr (Or.inr ⟨b, hb, hbc⟩))
  exact (realize_naturalZeroOrSuccessorBody _).mp (hi a ha)

end PolishSpaceBook.SetTheoryModels.AbstractMembership
