module

public import PolishSpaceBook.PCARealizabilityPER

@[expose] public section

/-! # Graph identities, composition, and equality of maps on representatives -/
namespace PolishSpaceBook.PCARealizability.RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

def Map.id (X : RealizerPER.{r,u} K) : Map X X := ⟨fun x => x,K.entails_refl _⟩

def Map.comp {X Y Z : RealizerPER.{r,u} K} (f : Map X Y) (g : Map Y Z) : Map X Z where
  toFun := g.toFun ∘ f.toFun
  preserves := g.map_of f.preserves

theorem Map.graph_id (X : RealizerPER.{r,u} K) :
    (Map.id X).graph.Equivalent (FunctionalRelation.identity X) :=
  FunctionalRelation.equivalent_of_le (K.and_right _ _)

theorem Map.graph_comp {X Y Z : RealizerPER.{r,u} K} (f : Map X Y) (g : Map Y Z) :
    (f.graph.comp g.graph).Equivalent (f.comp g).graph := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : (X.Carrier × Z.Carrier) × Y.Carrier → Set R :=
    K.predAnd (fun p => f.graph.val p.1.1 p.2) (fun p => g.graph.val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  exact K.and_intro (K.entails_trans (K.and_left _ _) (K.and_left _ _))
    (Z.trans_of (g.map_of (K.entails_trans (K.and_left _ _) (K.and_right _ _)))
      (K.entails_trans (K.and_right _ _) (K.and_right _ _)))

theorem Map.graph_equivalent_of_related {X Y : RealizerPER.{r,u} K} (f g : Map X Y)
    (h : K.Entails X.extent (fun x => Y.rel (f.toFun x) (g.toFun x))) :
    f.graph.Equivalent g.graph := by
  apply FunctionalRelation.equivalent_of_le
  exact K.and_intro (K.and_left _ _)
    (Y.trans_of (Y.symm_of (K.entails_trans (K.and_left _ _) (K.reindex_entails Prod.fst h)))
      (K.and_right _ _))

end PolishSpaceBook.PCARealizability.RealizerPER
