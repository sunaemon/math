module

public import PolishSpaceBook.LambdaRealizabilityFunctionData

@[expose] public section

/-! # Evaluation from numerical functional-relation data -/
namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER
universe u

section DataOperations
variable {X Y : RealizerPER.{u}} {I : Type*} {Γ : I → Set ℕ}
variable {R S : I → RawFunction X Y} {x x' : I → X.Carrier} {y y' : I → Y.Carrier}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For evaluation, an input realizer contains an extent realizer for $R$ and an element of $R(x,y)$.
    Extract the strictness index $s$ from the former and apply it to the latter. Its output gives $E_X(x)$ and $E_Y(y)$;
    together with the retained extent of $R$, this proves strictness of evaluation.
    For single-valuedness, extract $v$ and apply it to the two relation realizers at the same $x$.
    For extensionality, suppose the inputs also give $R\sim S$, $x\sim_X x'$, and $y\sim_Y y'$.
    The index $e$ from the data for $R$ transforms the $R(x,y)$ realizer into one for $R(x',y')$.
    The forward conversion in $R\sim S$ then gives an $S(x',y')$ realizer, and the PER laws give the extent of $S$.
    Pairing these outputs proves extensionality of evaluation.
-/
theorem data_strict_of (hd : Reduces Γ (fun i => functionData (R i)))
    (ha : Reduces Γ (fun i => R i (x i) (y i))) :
    Reduces Γ (realizabilityAnd (fun i => X.extent (x i)) (fun i => Y.extent (y i))) :=
  uniformImp_apply
    (φ := fun i (p : X.Carrier × Y.Carrier) => R i p.1 p.2)
    (ψ := fun _ => realizabilityAnd (fun p => X.extent p.1) (fun p => Y.extent p.2))
    (reduces_trans hd (reindex_reduces R data_strict)) (fun i => (x i, y i)) ha

theorem data_ext_of (hd : Reduces Γ (fun i => functionData (R i)))
    (hx : Reduces Γ (fun i => X.rel (x i) (x' i)))
    (ha : Reduces Γ (fun i => R i (x i) (y i)))
    (hy : Reduces Γ (fun i => Y.rel (y i) (y' i))) :
    Reduces Γ (fun i => R i (x' i) (y' i)) :=
  uniformImp_apply
    (φ := fun i => realizabilityAnd
      (realizabilityAnd (fun p : X.Carrier × X.Carrier × Y.Carrier × Y.Carrier => X.rel p.1 p.2.1)
        (fun p => R i p.1 p.2.2.1)) (fun p => Y.rel p.2.2.1 p.2.2.2))
    (ψ := fun i p => R i p.2.1 p.2.2.2)
    (reduces_trans hd (reindex_reduces R data_extensional))
    (fun i => (x i, x' i, y i, y' i)) (reduces_and_intro (reduces_and_intro hx ha) hy)

theorem data_single_of (hd : Reduces Γ (fun i => functionData (R i)))
    (ha : Reduces Γ (fun i => R i (x i) (y i)))
    (hb : Reduces Γ (fun i => R i (x i) (y' i))) : Reduces Γ (fun i => Y.rel (y i) (y' i)) :=
  uniformImp_apply
    (φ := fun i => realizabilityAnd (fun p : X.Carrier × Y.Carrier × Y.Carrier => R i p.1 p.2.1)
      (fun p => R i p.1 p.2.2)) (ψ := fun _ p => Y.rel p.2.1 p.2.2)
    (reduces_trans hd (reindex_reduces R data_single))
    (fun i => (x i, y i, y' i)) (reduces_and_intro ha hb)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Finally, an extent realizer for $(R,x)$ supplies the extent of $R$ and an $E_X(x)$ realizer $r$.
    Extract $t$ from the relation data and compute $b=t\cdot r$. There is some $y$ with $b\in R(x,y)$.
    Pairing $b$ with the retained extent of $R$ realizes $\evalMap((R,x),y)$.
    The program computes that pair; the existence of $y$ proves membership in the union required for totality.
    This verifies all four conditions for evaluation.
    \end{proof}
-/
theorem data_total_of (hd : Reduces Γ (fun i => functionData (R i)))
    (hx : Reduces Γ (fun i => X.extent (x i))) :
    Reduces Γ (fun i => {a | ∃ y, a ∈ R i (x i) y}) :=
  uniformImp_apply (φ := fun _ => X.extent) (ψ := fun i x => {a | ∃ y, a ∈ R i x y})
    (reduces_trans hd (reindex_reduces R data_total)) x hx

theorem functionEquality_apply (he : Reduces Γ (fun i => (functionSpace X Y).rel (R i) (S i)))
    (ha : Reduces Γ (fun i => R i (x i) (y i))) : Reduces Γ (fun i => S i (x i) (y i)) := by
  change Reduces Γ (realizabilityAnd
    (realizabilityAnd (fun i => functionData (R i)) (fun i => functionData (S i)))
    (realizabilityAnd (fun i => relationEntailment (R i) (S i)) (fun i => relationEntailment (S i) (R i)))) at he
  have hc : Reduces Γ (fun i => relationEntailment (R i) (S i)) :=
    reduces_trans (reduces_trans he (reduces_and_right _ _)) (reduces_and_left _ _)
  exact uniformImp_apply
    (φ := fun i (p : X.Carrier × Y.Carrier) => R i p.1 p.2) (ψ := fun i p => S i p.1 p.2)
    hc (fun i => (x i, y i)) ha

end DataOperations

/-- Evaluation retains the extent of the relation as well as its output realizer. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability function object}{Function object and evaluation}]
-/
def evaluation (X Y : RealizerPER.{u}) : FunctionalRelation (product (functionSpace X Y) X) Y where
  val p y := {a | a.unpair.1 ∈ (functionSpace X Y).extent p.1 ∧ a.unpair.2 ∈ p.1 p.2 y}
  strict := by
    let Γ : ((RawFunction X Y) × X.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (functionSpace X Y).extent p.1.1) (fun p => p.1.1 p.1.2 p.2)
    have hd : Reduces Γ (fun p => functionData p.1.1) :=
      extent_data_of (reduces_and_left _ _)
    have hs := data_strict_of hd (reduces_and_right _ _)
    exact reduces_and_intro (reduces_and_intro (reduces_and_left _ _)
      (reduces_trans hs (reduces_and_left _ _))) (reduces_trans hs (reduces_and_right _ _))
  extensional := by
    let Γ : ((RawFunction X Y) × X.Carrier) × ((RawFunction X Y) × X.Carrier) × Y.Carrier × Y.Carrier → Set ℕ :=
      realizabilityAnd (realizabilityAnd
        (fun p => (product (functionSpace X Y) X).rel p.1 p.2.1)
        (fun p => {a | a.unpair.1 ∈ (functionSpace X Y).extent p.1.1 ∧
          a.unpair.2 ∈ p.1.1 p.1.2 p.2.2.1}))
        (fun p => Y.rel p.2.2.1 p.2.2.2)
    have he : Reduces Γ (fun p => (functionSpace X Y).rel p.1.1 p.2.1.1) :=
      reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_left _ _)
    have hx : Reduces Γ (fun p => X.rel p.1.2 p.2.1.2) :=
      reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_right _ _)
    have hER : Reduces Γ (fun p => (functionSpace X Y).extent p.1.1) :=
      reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_left _ _)
    have hd : Reduces Γ (fun p => functionData p.1.1) :=
      extent_data_of hER
    have ha : Reduces Γ (fun p => p.1.1 p.1.2 p.2.2.1) :=
      reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_right _ _)
    have hb := data_ext_of hd hx ha (reduces_and_right _ _)
    exact reduces_and_intro ((functionSpace X Y).extent_right_of he) (functionEquality_apply he hb)
  single := by
    let Γ : ((RawFunction X Y) × X.Carrier) × Y.Carrier × Y.Carrier → Set ℕ :=
      realizabilityAnd
        (fun p => {a | a.unpair.1 ∈ (functionSpace X Y).extent p.1.1 ∧ a.unpair.2 ∈ p.1.1 p.1.2 p.2.1})
        (fun p => {a | a.unpair.1 ∈ (functionSpace X Y).extent p.1.1 ∧ a.unpair.2 ∈ p.1.1 p.1.2 p.2.2})
    have hd : Reduces Γ (fun p => functionData p.1.1) :=
      extent_data_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
    exact data_single_of hd (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  total := by
    let Γ : (RawFunction X Y) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (functionSpace X Y).extent p.1) (fun p => X.extent p.2)
    have hd : Reduces Γ (fun p => functionData p.1) :=
      extent_data_of (reduces_and_left _ _)
    have ht := data_total_of hd (reduces_and_right _ _)
    apply reduces_trans (reduces_and_intro (reduces_and_left _ _) ht)
    exact reduces_of_subset fun p _ h => by
      rcases h with ⟨hE, y, hy⟩
      exact ⟨y, hE, hy⟩

end PolishSpaceBook.LambdaIndexPCA
