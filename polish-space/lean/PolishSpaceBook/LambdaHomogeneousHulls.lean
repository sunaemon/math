module

public import PolishSpaceBook.LambdaInvariantSeparation
public import PolishSpaceBook.SilverKernel

@[expose] public section

/-! # Homogeneous hulls and the Silver remainder at a fixed lambda parameter -/

namespace PolishSpaceBook
open Set MeasureTheory
namespace LambdaTree

/-- The book's universal class is the complement of a relative analytic
relational image. Separation supplies both codes for its homogeneous hull. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use $D_e,D'_e$ from the complemented-code construction, so that for valid $e$ they are complements.
    Let
    $$\begin{aligned}
    B_e&:=\{(u,v):u,v\in D_e,\ u\mathrel{\not E}v\},\\
    J_e&:=\{x:e\notin C\},\qquad K_e:=\{x:B_e\ne\emptyset\}.
    \end{aligned}$$
    The relation $\neg E$ has an analytic presentation. Pulling back $D_e$ along both coordinates and
    intersecting with that presentation gives a joint tree family for $B_e$. The invalid-code construction
    gives $J_e$, and the nonemptiness construction gives $K_e$. All use the fixed parameter. Now
    $$H=X\cap\bigcap_e(J_e\cup K_e\cup D'_e).$$
    Indeed, an invalid code imposes no restriction. For a valid code, $K_e$ is the whole space precisely
    when $D_e$ is not homogeneous. Otherwise the test requires membership in $D'_e$, which excludes $D_e$.
    Soundness and completeness of the complemented codes identify this intersection with the definition
    of $H$. The uniform union and intersection constructions give the claimed analytic presentation;
    restriction to the fixed closed presentation preserves it.

    Suppose $A\IncludedIn H$ is nonempty, analytic, and homogeneous. The relational image
    $$R_A:=\{y:\exists x\in A\ (x\mathrel{\not E}y)\}$$
    is analytic and disjoint from $A$. Effective separation constructs a set $D$ and its complement at
    the same parameter, with $A\IncludedIn D\IncludedIn R_A^{\complement}$. Fix $a\in A$.
    Every point of $D$ is equivalent to $a$, so symmetry and transitivity make $D$ homogeneous.
    Completeness supplies a valid code for this hull. Thus $D$ occurs in the union removed from $H$,
    contradicting the nonempty inclusion $A\IncludedIn H\cap D$.
    \end{proof}
-/
theorem homogeneous_hull {ε : ℕ → ℕ} (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y)) {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hne : A.Nonempty) (hhom : ERHomogeneous E A) :
    ∃ D, Complemented ε D ∧ A ⊆ D ∧
      (∀ y ∈ D, ∀ x ∈ A, E.r x y) ∧ ERHomogeneous E D := by
  have hbad := projected_relationalImage hE hA
  have hd : Disjoint A {y | ∃ x ∈ A, ¬ E.r x y} := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨x, hx, hxy⟩
    exact hxy (hhom x hx y hy)
  obtain ⟨D, hc, hAD, hDB⟩ := effective_separation hA hbad hd
  have hclass : ∀ y ∈ D, ∀ x ∈ A, E.r x y := by
    intro y hy x hx
    by_contra hxy
    exact hDB hy ⟨x, hx, hxy⟩
  refine ⟨D, hc, hAD, hclass, ?_⟩
  obtain ⟨a, ha⟩ := hne
  intro x hx y hy
  exact E.trans (E.symm (hclass x hx a ha)) (hclass y hy a ha)

/-- All homogeneous sets with complementary tree codes, without selecting
an enumeration or extending the parameter. -/
def HomogeneousSet (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ)) :=
  {D : Set (ℕ → ℕ) // Complemented ε D ∧ ERHomogeneous E D}

def silverKernel (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  homogeneousRemainder (fun D : HomogeneousSet ε E => D.val)

theorem mem_silverKernel_iff (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ)) (x : ℕ → ℕ) :
    x ∈ silverKernel ε E ↔
      ∀ D, Complemented ε D → ERHomogeneous E D → x ∉ D := by
  constructor
  · intro hx D hc hh hxD
    exact hx (Set.mem_iUnion.mpr ⟨⟨D, hc, hh⟩, hxD⟩)
  · intro hx hi
    obtain ⟨D, hxD⟩ := Set.mem_iUnion.mp hi
    exact hx D.val D.property.1 D.property.2 hxD

theorem countable_homogeneousSet (ε : ℕ → ℕ)
    (E : Setoid (ℕ → ℕ)) : Countable (HomogeneousSet ε E) :=
  ((countable_projected ε).mono fun _ h => h.1.1).to_subtype

theorem silverKernel_nonempty (ε : ℕ → ℕ)
    (E : Setoid (ℕ → ℕ)) [Uncountable (Quotient E)] : (silverKernel ε E).Nonempty := by
  let := countable_homogeneousSet ε E
  exact homogeneousRemainder_nonempty E (fun D : HomogeneousSet ε E => D.val)
    (fun D => D.property.2)

/-- This is ordinary Borel measurability, not relative analytic membership. -/
theorem silverKernel_measurable (ε : ℕ → ℕ)
    (E : Setoid (ℕ → ℕ)) : MeasurableSet (silverKernel ε E) := by
  let := countable_homogeneousSet ε E
  exact homogeneousRemainder_measurable (fun D : HomogeneousSet ε E => D.val)
    (fun D => D.property.1.measurableSet)

/-- The hereditary conclusion does not assume that the new kernel belongs
to the relative catalog. `LambdaKernelComplexity` proves that separate
complexity assertion. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use $D_e,D'_e$ from the complemented-code construction, so that for valid $e$ they are complements.
    Let
    $$\begin{aligned}
    B_e&:=\{(u,v):u,v\in D_e,\ u\mathrel{\not E}v\},\\
    J_e&:=\{x:e\notin C\},\qquad K_e:=\{x:B_e\ne\emptyset\}.
    \end{aligned}$$
    The relation $\neg E$ has an analytic presentation. Pulling back $D_e$ along both coordinates and
    intersecting with that presentation gives a joint tree family for $B_e$. The invalid-code construction
    gives $J_e$, and the nonemptiness construction gives $K_e$. All use the fixed parameter. Now
    $$H=X\cap\bigcap_e(J_e\cup K_e\cup D'_e).$$
    Indeed, an invalid code imposes no restriction. For a valid code, $K_e$ is the whole space precisely
    when $D_e$ is not homogeneous. Otherwise the test requires membership in $D'_e$, which excludes $D_e$.
    Soundness and completeness of the complemented codes identify this intersection with the definition
    of $H$. The uniform union and intersection constructions give the claimed analytic presentation;
    restriction to the fixed closed presentation preserves it.

    Suppose $A\IncludedIn H$ is nonempty, analytic, and homogeneous. The relational image
    $$R_A:=\{y:\exists x\in A\ (x\mathrel{\not E}y)\}$$
    is analytic and disjoint from $A$. Effective separation constructs a set $D$ and its complement at
    the same parameter, with $A\IncludedIn D\IncludedIn R_A^{\complement}$. Fix $a\in A$.
    Every point of $D$ is equivalent to $a$, so symmetry and transitivity make $D$ homogeneous.
    Completeness supplies a valid code for this hull. Thus $D$ occurs in the union removed from $H$,
    contradicting the nonempty inclusion $A\IncludedIn H\cap D$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{lemma*}[Silver kernel]
-/
theorem silverKernel_not_homogeneous {ε : ℕ → ℕ} (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y)) {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hne : A.Nonempty) (hAH : A ⊆ silverKernel ε E) :
    ¬ ERHomogeneous E A := by
  intro hhom
  obtain ⟨D, hc, hAD, _, hh⟩ := homogeneous_hull E hE hA hne hhom
  obtain ⟨x, hx⟩ := hne
  exact (mem_silverKernel_iff ε E x).mp (hAH hx) D hc hh (hAD hx)

end LambdaTree
end PolishSpaceBook
