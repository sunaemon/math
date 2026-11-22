module

public import PolishSpaceBook.PCARealizabilitySubobjects

@[expose] public section

/-! # Characteristic relations over a PCA

Truth values and characteristic maps use only the shared implication adjunction.
The truth object separates uniform predicate classes, which will detect whether
an image is the whole codomain without assuming a topos instance.
-/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

theorem imp_apply_of {I : Type*} {Γ φ ψ : I → Set R}
    (hf : K.Entails Γ (K.predImp φ ψ)) (ha : K.Entails Γ φ) : K.Entails Γ ψ :=
  K.entails_trans (K.and_intro hf ha) ((K.imp_adjunction _ φ ψ).mpr (K.entails_refl _))

theorem imp_comp_of {I : Type*} {Γ φ ψ θ : I → Set R}
    (h₁ : K.Entails Γ (K.predImp φ ψ)) (h₂ : K.Entails Γ (K.predImp ψ θ)) :
    K.Entails Γ (K.predImp φ θ) := by
  apply (K.imp_adjunction _ _ _).mp
  exact imp_apply_of (K.entails_trans (K.and_left _ _) h₂)
    (imp_apply_of (K.entails_trans (K.and_left _ _) h₁) (K.and_right _ _))

theorem imp_identity {I : Type*} (Γ φ : I → Set R) : K.Entails Γ (K.predImp φ φ) :=
  (K.imp_adjunction _ _ _).mp (K.and_right _ _)

def truthImp (S T : Set R) : Set R :=
  {e | ∀ a, a ∈ S → ∃ b, K.application e a = Part.some b ∧ b ∈ T}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{mathmeta}
      \define{PCATruthValues}
    \end{mathmeta}
    For the converse, use the truth-value PER $\PCATruthValues{A}$ on $\PowerSet{A}$, with
    $$S\sim_\Omega T:=(S\to T)\land(T\to S).$$
    The implication adjunction gives the equality-preserving map $y\mapsto\varphi(y)$ for every strict
    extensional predicate $\varphi$. Its graph is
    $$\chi_\varphi(y,S):=E_Y(y)\land\bigl(\varphi(y)\sim_\Omega S\bigr).$$
    If $\chi_\varphi=\chi_\psi$, an input $a\in\varphi(y)$ first gives a realizer of
    $\chi_\varphi(y,\varphi(y))$ by strictness and the identity implications. Transform it into a realizer
    of $\chi_\psi(y,\varphi(y))$ and apply the implication $\varphi(y)\to\psi(y)$ to $a$.
    This gives $\varphi\le\psi$ uniformly, and reversing the arrows gives $\psi\le\varphi$.
-/
def truthValues : RealizerPER.{r,max r u} K where
  Carrier := ULift.{u} (Set R)
  rel S T := {a | ∃ b c, a = K.pair b c ∧ b ∈ truthImp (K := K) S.down T.down ∧
    c ∈ truthImp (K := K) T.down S.down}
  symmetry := K.and_intro (K.and_right _ _) (K.and_left _ _)
  transitivity := K.and_intro
    (imp_comp_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
    (imp_comp_of (K.entails_trans (K.and_right _ _) (K.and_right _ _))
      (K.entails_trans (K.and_left _ _) (K.and_right _ _)))

theorem truth_extent {I : Type*} (Γ : I → Set R) (S : I → (truthValues.{r,u} (K := K)).Carrier) :
    K.Entails Γ (fun i => (truthValues.{r,u} (K := K)).extent (S i)) :=
  K.and_intro (imp_identity Γ (fun i => (S i).down)) (imp_identity Γ (fun i => (S i).down))

def characteristicMap {X : RealizerPER.{r,max r u} K} (P : StrictPredicate X) :
    Map X (truthValues.{r,u} (K := K)) where
  toFun x := ⟨P.val x⟩
  preserves := by
    apply K.and_intro
    · exact (K.imp_adjunction _ _ _).mp P.extensional
    · apply (K.imp_adjunction _ _ _).mp
      exact K.entails_trans (K.and_intro (X.symm_of (K.and_left _ _)) (K.and_right _ _))
        (K.reindex_entails (fun p : X.Carrier × X.Carrier => (p.2,p.1)) P.extensional)

abbrev characteristic {X : RealizerPER.{r,max r u} K} (P : StrictPredicate X) :=
  (characteristicMap.{r,u} P).graph

/-- Evaluate the second implication at the predicate's own truth value. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{mathmeta}
      \define{PCATruthValues}
    \end{mathmeta}
    For the converse, use the truth-value PER $\PCATruthValues{A}$ on $\PowerSet{A}$, with
    $$S\sim_\Omega T:=(S\to T)\land(T\to S).$$
    The implication adjunction gives the equality-preserving map $y\mapsto\varphi(y)$ for every strict
    extensional predicate $\varphi$. Its graph is
    $$\chi_\varphi(y,S):=E_Y(y)\land\bigl(\varphi(y)\sim_\Omega S\bigr).$$
    If $\chi_\varphi=\chi_\psi$, an input $a\in\varphi(y)$ first gives a realizer of
    $\chi_\varphi(y,\varphi(y))$ by strictness and the identity implications. Transform it into a realizer
    of $\chi_\psi(y,\varphi(y))$ and apply the implication $\varphi(y)\to\psi(y)$ to $a$.
    This gives $\varphi\le\psi$ uniformly, and reversing the arrows gives $\psi\le\varphi$.
-/
theorem predicate_entails_of_characteristic_le {X : RealizerPER.{r,max r u} K}
    (P Q : StrictPredicate X) (h : (characteristic.{r,u} P).LE (characteristic.{r,u} Q)) :
    K.Entails P.val Q.val := by
  have hP : K.Entails P.val (fun x => (characteristic.{r,u} P).val x ⟨P.val x⟩) :=
    K.and_intro P.strict (truth_extent.{r,u} _ (fun x => ⟨P.val x⟩))
  have hQ := K.entails_trans hP (K.reindex_entails (fun x : X.Carrier => (x,(⟨P.val x⟩ : (truthValues.{r,u} (K := K)).Carrier))) h)
  exact imp_apply_of (K.entails_trans (K.entails_trans hQ (K.and_right _ _)) (K.and_right _ _))
    (K.entails_refl _)

theorem predicate_equivalent_of_characteristic_eq {X : RealizerPER.{r,max r u} K}
    (P Q : StrictPredicate X) (h : (characteristic.{r,u} P).toHom = (characteristic.{r,u} Q).toHom) :
    K.Entails P.val Q.val ∧ K.Entails Q.val P.val := by
  obtain ⟨hPQ,hQP⟩ := (FunctionalRelation.toHom_eq_iff _ _).mp h
  exact ⟨predicate_entails_of_characteristic_le P Q hPQ,
    predicate_entails_of_characteristic_le Q P hQP⟩

end PolishSpaceBook.PCARealizability
