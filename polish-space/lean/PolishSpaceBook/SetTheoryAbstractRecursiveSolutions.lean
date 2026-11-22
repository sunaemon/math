module

public import PolishSpaceBook.SetTheoryAbstractHulls

@[expose] public section

/-! # Agreement and gluing of internal recursive solutions -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def IsRestriction (f A g : M) : Prop :=
  IsGraphOn g A ∧ ∀ a b : M, GraphApplication g a b ↔ member a A ∧ GraphApplication f a b

theorem graphOn_ext (hext : M ⊨ extensionalitySentence) {A f g : M}
    (hf : IsGraphOn f A) (hg : IsGraphOn g A)
    (he : ∀ a b c : M, GraphApplication f a b → GraphApplication g a c → b = c) : f = g := by
  apply functionGraph_ext hext hf.1 hg.1
  intro a b
  constructor
  · intro hab
    obtain ⟨c, hac⟩ := (hg.2 a).mpr ((hf.2 a).mp ⟨b, hab⟩)
    exact (he a b c hab hac).symm ▸ hac
  · intro hab
    obtain ⟨c, hac⟩ := (hf.2 a).mpr ((hg.2 a).mp ⟨b, hab⟩)
    exact he a c b hac hab ▸ hac

theorem exists_restriction (hM : M ⊨ fullZFCTheory) {f A D : M}
    (hf : IsGraphOn f D) (hAD : ∀ a : M, member a A → member a D) :
    ∃ g : M, IsRestriction f A g := by
  obtain ⟨g, hg⟩ := exists_graphRestriction hM f A
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  exact ⟨g, isGraphOn_restriction hext hf hAD hg, graphApplication_restriction hext hg⟩

def IsRecursiveSolution (R : M → M → M → Prop) (D f : M) : Prop :=
  IsTransitiveObject D ∧ IsGraphOn f D ∧
    ∀ a : M, member a D → ∃ g b : M, IsRestriction f a g ∧ GraphApplication f a b ∧ R a g b

/-- Membership induction is applied to the concrete graph-agreement formula.
The interpreted relation need not itself encode external well-foundedness. -/
theorem recursiveSolutions_agree (hM : M ⊨ fullZFCTheory) {R : M → M → M → Prop}
    (hR : ∀ a g b c : M, R a g b → R a g c → b = c)
    {D E f g : M} (hf : IsRecursiveSolution R D f) (hg : IsRecursiveSolution R E g) :
    ∀ a b c : M, GraphApplication f a b → GraphApplication g a c → b = c := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hi := fullZFC_definable_induction graphAgreementBody hM ![f, g] D hf.1
    (fun a haD ih => (realize_graphAgreementBody _).mpr (by
      intro b c hab hac
      have haE := (hg.2.1.2 a).mp ⟨c, hac⟩
      obtain ⟨r, b', hr, hab', hb'⟩ := hf.2.2 a haD
      obtain ⟨t, c', ht, hac', hc'⟩ := hg.2.2 a haE
      have hrt : r = t := by
        apply graphOn_ext hext hr.1 ht.1
        intro x y z hxy hxz
        obtain ⟨hxa, hfxy⟩ := (hr.2 x y).mp hxy
        have hgxz := ((ht.2 x z).mp hxz).2
        exact (realize_graphAgreementBody _).mp (ih x hxa) y z hfxy hgxz
      subst t
      exact (hf.2.1.1.2 a b b' hab hab').trans
        ((hR a r b' c' hb' hc').trans (hg.2.1.1.2 a c' c hac' hac))))
  intro a b c hab hac
  exact (realize_graphAgreementBody _).mp (hi a ((hf.2.1.2 a).mp ⟨b, hab⟩)) b c hab hac

theorem recursiveSolution_unique (hM : M ⊨ fullZFCTheory) {R : M → M → M → Prop}
    (hR : ∀ a g b c : M, R a g b → R a g c → b = c)
    {D f g : M} (hf : IsRecursiveSolution R D f) (hg : IsRecursiveSolution R D g) : f = g :=
  graphOn_ext (hM.realize_of_mem _ ZFCAxiom.extensionality) hf.2.1 hg.2.1
    (recursiveSolutions_agree hM hR hf hg)

/-- Any internal set of compatible recursive graphs can be glued by Union;
the exact domain is then obtained by the derived graph-domain operation. -/
theorem recursiveSolutions_union (hM : M ⊨ fullZFCTheory) {R : M → M → M → Prop}
    (hR : ∀ a g b c : M, R a g b → R a g c → b = c)
    (F : M) (hF : ∀ f : M, member f F → ∃ D : M, IsRecursiveSolution R D f) :
    ∃ U H : M, IsRecursiveSolution R U H ∧
      (∀ a b : M, GraphApplication H a b ↔ ∃ f : M, member f F ∧ GraphApplication f a b) := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hunion := hM.realize_of_mem _ ZFCAxiom.union
  obtain ⟨H, hH⟩ := (models_union_iff M).mp hunion F
  have happ (a b : M) : GraphApplication H a b ↔ ∃ f : M, member f F ∧ GraphApplication f a b := by
    constructor
    · rintro ⟨q, hq, hqH⟩
      obtain ⟨f, hqf, hfF⟩ := (hH q).mp hqH
      exact ⟨f, hfF, q, hq, hqf⟩
    · rintro ⟨f, hfF, q, hq, hqf⟩
      exact ⟨q, hq, (hH q).mpr ⟨f, hqf, hfF⟩⟩
  have hfunction : IsFunctionGraph H := by
    constructor
    · intro q hqH
      obtain ⟨f, hqf, hfF⟩ := (hH q).mp hqH
      obtain ⟨D, hf⟩ := hF f hfF
      exact hf.2.1.1.1 q hqf
    · intro a b c hab hac
      obtain ⟨f, hfF, hfab⟩ := (happ a b).mp hab
      obtain ⟨g, hgF, hgac⟩ := (happ a c).mp hac
      obtain ⟨D, hf⟩ := hF f hfF
      obtain ⟨E, hg⟩ := hF g hgF
      exact recursiveSolutions_agree hM hR hf hg a b c hfab hgac
  obtain ⟨U, hU, _⟩ := existsUnique_graphDomain hext hunion (fullZFC_model_separation hM _) H
  have hgraph : IsGraphOn H U := ⟨hfunction, fun a => (hU a).symm⟩
  have htrans : IsTransitiveObject U := by
    intro a ha b hba
    obtain ⟨c, hac⟩ := (hU a).mp ha
    obtain ⟨f, hfF, hfac⟩ := (happ a c).mp hac
    obtain ⟨D, hf⟩ := hF f hfF
    have hbD := hf.1 a ((hf.2.1.2 a).mp ⟨c, hfac⟩) b hba
    obtain ⟨d, hfbd⟩ := (hf.2.1.2 b).mpr hbD
    exact (hU b).mpr ⟨d, (happ b d).mpr ⟨f, hfF, hfbd⟩⟩
  refine ⟨U, H, ⟨htrans, hgraph, ?_⟩, happ⟩
  intro a haU
  obtain ⟨c, hac⟩ := (hU a).mp haU
  obtain ⟨f, hfF, hfac⟩ := (happ a c).mp hac
  obtain ⟨D, hf⟩ := hF f hfF
  obtain ⟨r, b, hr, hfab, hb⟩ := hf.2.2 a ((hf.2.1.2 a).mp ⟨c, hfac⟩)
  obtain ⟨t, ht⟩ := exists_restriction hM hgraph (htrans a haU)
  have htr : t = r := by
    apply graphOn_ext hext ht.1 hr.1
    intro x y z htxy hrxz
    have hHxy := ((ht.2 x y).mp htxy).2
    have hfxz := ((hr.2 x z).mp hrxz).2
    obtain ⟨g, hgF, hgxy⟩ := (happ x y).mp hHxy
    obtain ⟨E, hg⟩ := hF g hgF
    exact recursiveSolutions_agree hM hR hg hf x y z hgxy hfxz
  subst t
  exact ⟨r, b, ht, (happ a b).mpr ⟨f, hfF, hfab⟩, hb⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
