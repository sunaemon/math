module

public import PolishSpaceBook.SetTheoryAbstractOmega

@[expose] public section

/-! # Internal function graphs in arbitrary membership models

Graph extension and restriction use actual Pairing, Union, and Separation
instances. All pair comparisons refer to the model's interpreted membership.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

theorem kuratowskiPair_unique (hext : M ⊨ extensionalitySentence) {q r a b : M}
    (hq : IsKuratowskiPair q a b) (hr : IsKuratowskiPair r a b) : q = r := by
  obtain ⟨s, p, hs, hp, hq⟩ := hq
  obtain ⟨s', p', hs', hp', hr⟩ := hr
  have hss := unorderedPair_unique hext hs' hs
  have hpp := unorderedPair_unique hext hp' hp
  subst s'
  subst p'
  exact unorderedPair_unique hext hq hr

theorem kuratowskiPair_coordinates (hext : M ⊨ extensionalitySentence) {q a b c d : M}
    (hab : IsKuratowskiPair q a b) (hcd : IsKuratowskiPair q c d) : a = c ∧ b = d := by
  obtain ⟨s, p, hs, hp, hq⟩ := hab
  obtain ⟨t, r, ht, hr, hq'⟩ := hcd
  have hcs : member c s := by
    rcases (hq' s).mp ((hq s).mpr (Or.inl rfl)) with rfl | rfl
    · exact (ht c).mpr (Or.inl rfl)
    · exact (hr c).mpr (Or.inl rfl)
  have hca : c = a := (hs c).mp hcs |>.elim id id
  subst c
  refine ⟨rfl, ?_⟩
  by_cases hba : b = a
  · subst b
    have hps := unorderedPair_unique hext hp hs
    subst p
    have hrs : r = s := (hq r).mp ((hq' r).mpr (Or.inr rfl)) |>.elim id id
    subst r
    have hda : d = a := (hs d).mp ((hr d).mpr (Or.inr rfl)) |>.elim id id
    exact hda.symm
  · have hb : b = a ∨ b = d := by
      rcases (hq' p).mp ((hq p).mpr (Or.inr rfl)) with hpt | hpr
      · exact Or.inl ((ht b).mp (hpt ▸ (hp b).mpr (Or.inr rfl)) |>.elim id id)
      · exact (hr b).mp (hpr ▸ (hp b).mpr (Or.inr rfl))
    exact hb.resolve_left hba

def IsGraphOn (f A : M) : Prop :=
  IsFunctionGraph f ∧ ∀ a : M, (∃ b : M, GraphApplication f a b) ↔ member a A

theorem isGraphOn_empty {e : M} (he : IsEmptyObject e) : IsGraphOn e e := by
  refine ⟨⟨fun q hq => False.elim (he q hq), ?_⟩, ?_⟩
  · rintro a b c ⟨q, _, hq⟩ _
    exact False.elim (he q hq)
  · intro a
    constructor
    · rintro ⟨b, q, _, hq⟩
      exact False.elim (he q hq)
    · intro ha
      exact False.elim (he a ha)

theorem functionGraph_ext (hext : M ⊨ extensionalitySentence) {f g : M}
    (hf : IsFunctionGraph f) (hg : IsFunctionGraph g)
    (he : ∀ a b : M, GraphApplication f a b ↔ GraphApplication g a b) : f = g := by
  apply (models_extensionality_iff M).mp hext f g
  intro q
  constructor
  · intro hq
    obtain ⟨a, b, hab⟩ := hf.1 q hq
    obtain ⟨r, hr, hrg⟩ := (he a b).mp ⟨q, hab, hq⟩
    exact kuratowskiPair_unique hext hr hab ▸ hrg
  · intro hq
    obtain ⟨a, b, hab⟩ := hg.1 q hq
    obtain ⟨r, hr, hrf⟩ := (he a b).mpr ⟨q, hab, hq⟩
    exact kuratowskiPair_unique hext hr hab ▸ hrf

/-- Adjoin one ordered pair, preserving a literal membership characterization. -/
theorem exists_graphInsert (hM : M ⊨ fullZFCTheory) (f a b : M) :
    ∃ g : M, ∀ q : M, member q g ↔ member q f ∨ IsKuratowskiPair q a b := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  obtain ⟨p, hpair, _⟩ := existsUnique_kuratowskiPair hext hp a b
  obtain ⟨s, hs, _⟩ := existsUnique_pair hext hp p p
  obtain ⟨g, hg, _⟩ := existsUnique_binaryUnion hext hp
    (hM.realize_of_mem _ ZFCAxiom.union) f s
  refine ⟨g, fun q => ?_⟩
  rw [hg q, hs q, or_self]
  exact or_congr Iff.rfl ⟨fun h => h ▸ hpair, fun h => kuratowskiPair_unique hext h hpair⟩

theorem graphApplication_insert (hext : M ⊨ extensionalitySentence)
    (hp : M ⊨ pairingSentence) {f g a b : M}
    (hg : ∀ q : M, member q g ↔ member q f ∨ IsKuratowskiPair q a b) (x y : M) :
    GraphApplication g x y ↔ GraphApplication f x y ∨ x = a ∧ y = b := by
  constructor
  · rintro ⟨q, hq, hqg⟩
    rcases (hg q).mp hqg with hqf | hab
    · exact Or.inl ⟨q, hq, hqf⟩
    · exact Or.inr (kuratowskiPair_coordinates hext hq hab)
  · rintro (h | ⟨rfl, rfl⟩)
    · obtain ⟨q, hq, hqf⟩ := h
      exact ⟨q, hq, (hg q).mpr (Or.inl hqf)⟩
    · obtain ⟨q, hq, _⟩ := existsUnique_kuratowskiPair hext hp x y
      exact ⟨q, hq, (hg q).mpr (Or.inr hq)⟩

theorem isGraphOn_insert (hM : M ⊨ fullZFCTheory) {f g A B a b : M}
    (hf : IsGraphOn f A) (ha : ¬member a A)
    (hB : ∀ x : M, member x B ↔ member x A ∨ x = a)
    (hg : ∀ q : M, member q g ↔ member q f ∨ IsKuratowskiPair q a b) : IsGraphOn g B := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have happ := graphApplication_insert hext (hM.realize_of_mem _ ZFCAxiom.pairing) hg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q hq
    rcases (hg q).mp hq with hq | hq
    · exact hf.1.1 q hq
    · exact ⟨a, b, hq⟩
  · intro x y z hy hz
    rcases (happ x y).mp hy with hy | ⟨hxa, hyb⟩
    · rcases (happ x z).mp hz with hz | ⟨hxa, hzb⟩
      · exact hf.1.2 x y z hy hz
      · exact False.elim (ha (hxa ▸ (hf.2 x).mp ⟨y, hy⟩))
    · subst x
      rcases (happ a z).mp hz with hz | ⟨_, hzb⟩
      · exact False.elim (ha ((hf.2 a).mp ⟨z, hz⟩))
      · exact hyb.trans hzb.symm
  · intro x
    rw [hB x]
    constructor
    · rintro ⟨y, hy⟩
      rcases (happ x y).mp hy with hy | ⟨hxa, _⟩
      · exact Or.inl ((hf.2 x).mp ⟨y, hy⟩)
      · exact Or.inr hxa
    · rintro (hx | hxa)
      · obtain ⟨y, hy⟩ := (hf.2 x).mpr hx
        exact ⟨y, (happ x y).mpr (Or.inl hy)⟩
      · subst x
        exact ⟨b, (happ a b).mpr (Or.inr ⟨rfl, rfl⟩)⟩

def graphRestrictionMemberBody : ForcingFormulas.Formula 2 :=
  (memberAt (2 : Fin 4) 0 ⊓ internalKuratowskiFormula 1 2 3).ex.ex

theorem realize_graphRestrictionMemberBody (xs : Fin 2 → M) :
    graphRestrictionMemberBody.Realize Empty.elim xs ↔
      ∃ a b : M, member a (xs 0) ∧ IsKuratowskiPair (xs 1) a b := by
  simp [graphRestrictionMemberBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_memberAt, realize_internalKuratowskiFormula, Fin.snoc]

theorem exists_graphRestriction (hM : M ⊨ fullZFCTheory) (f A : M) :
    ∃ g : M, ∀ q : M, member q g ↔ member q f ∧
      ∃ a b : M, member a A ∧ IsKuratowskiPair q a b := by
  obtain ⟨g, hg⟩ := (realize_separation M graphRestrictionMemberBody).mp
    (fullZFC_model_separation hM _) ![A] f
  refine ⟨g, fun q => ?_⟩
  simpa [realize_graphRestrictionMemberBody, Fin.snoc] using hg q

theorem graphApplication_restriction (hext : M ⊨ extensionalitySentence) {f g A : M}
    (hg : ∀ q : M, member q g ↔ member q f ∧
      ∃ a b : M, member a A ∧ IsKuratowskiPair q a b) (x y : M) :
    GraphApplication g x y ↔ member x A ∧ GraphApplication f x y := by
  constructor
  · rintro ⟨q, hq, hqg⟩
    obtain ⟨hqf, a, b, ha, hab⟩ := (hg q).mp hqg
    obtain ⟨rfl, rfl⟩ := kuratowskiPair_coordinates hext hq hab
    exact ⟨ha, q, hq, hqf⟩
  · rintro ⟨hx, q, hq, hqf⟩
    exact ⟨q, hq, (hg q).mpr ⟨hqf, x, y, hx, hq⟩⟩

theorem isGraphOn_restriction (hext : M ⊨ extensionalitySentence) {f g A B : M}
    (hf : IsGraphOn f B) (hAB : ∀ x : M, member x A → member x B)
    (hg : ∀ q : M, member q g ↔ member q f ∧
      ∃ a b : M, member a A ∧ IsKuratowskiPair q a b) : IsGraphOn g A := by
  have happ := graphApplication_restriction hext hg
  refine ⟨⟨fun q hq => hf.1.1 q ((hg q).mp hq).1, ?_⟩, ?_⟩
  · intro a b c hb hc
    exact hf.1.2 a b c ((happ a b).mp hb).2 ((happ a c).mp hc).2
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((happ a b).mp hb).1
    · intro ha
      obtain ⟨b, hb⟩ := (hf.2 a).mpr (hAB a ha)
      exact ⟨b, (happ a b).mpr ⟨ha, hb⟩⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
