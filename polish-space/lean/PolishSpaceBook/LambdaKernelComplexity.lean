module

public import PolishSpaceBook.LambdaUniformFamilies
public import PolishSpaceBook.LambdaHomogeneousHulls
public import PolishSpaceBook.LambdaInvariantKernel

@[expose] public section

/-! # Lambda tree presentations of the Silver and HKL kernels

Invalidity, failure of homogeneity, and failure of invariance are witnessed
by branches. No program deciding these semantic conditions is assumed.
-/

namespace PolishSpaceBook
open Set
namespace LambdaTree

/-- The Silver remainder itself belongs to the original relative analytic
catalog. The only relation hypothesis is relative coanalyticity of E. -/
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
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    In the kernel arguments, invalidity and failures of homogeneity or invariance will enter as analytic
    alternatives, uniformly in the code. This interface uses separation directly and does not require a
    completeness theorem for a separate Borel-expression syntax.
-/
theorem projected_silverKernel (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y)) :
    Projected ε
      (silverKernel ε E) := by
  classical
  obtain ⟨C⟩ := exists_complementedCodes ε
  let bad := fun n => {p | leftBaire p ∈ C.positiveSet n} ∩
    {p | rightBaire p ∈ C.positiveSet n} ∩ {p | ¬ E.r (leftBaire p) (rightBaire p)}
  have hb : UniformProjected ε bad :=
    (C.uniform_positive.left.inter C.uniform_positive.right).inter (.const hneE)
  have hbad (n : ℕ) : (bad n).Nonempty ↔ ¬ ERHomogeneous E (C.positiveSet n) := by
    constructor
    · rintro ⟨p, ⟨hl, hr⟩, hn⟩ hh
      exact hn (hh _ hl _ hr)
    · intro hn
      simp only [ERHomogeneous, not_forall] at hn
      obtain ⟨x, hx, y, hy, hxy⟩ := hn
      exact ⟨pairBaire x y, by simpa [bad] using And.intro (And.intro hx hy) hxy⟩
  have h := ((uniform_invalidComplementedIndex ε).union hb.nonempty).union C.uniform_negative
  have heq : (⋂ n, ({_x | ¬ ValidComplementedIndex ε n} ∪
      {_x | (bad n).Nonempty}) ∪ C.negativeSet n) =
      silverKernel ε E := by
    ext x
    simp only [mem_iInter, mem_union, mem_ofPred_eq, hbad, mem_silverKernel_iff]
    constructor
    · intro hx D hc hh
      obtain ⟨n, hn, rfl⟩ := C.complete hc
      have hneg := (hx n).resolve_left (by tauto)
      rw [C.complementary hn]
      exact fun h => h hneg
    · intro hx n
      by_cases hv : ValidComplementedIndex ε n
      · by_cases hh : ERHomogeneous E (C.positiveSet n)
        · apply Or.inr
          have hn := hx _ (C.sound hv) hh
          simpa only [C.complementary hv, mem_compl_iff, not_not] using hn
        · exact Or.inl (Or.inr hh)
      · exact Or.inl (Or.inl hv)
  exact heq ▸ h.iInter

/-- The actual invariant-test relation is relatively analytic whenever E is.
No code for the larger relation is supplied as an extra hypothesis. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    It contains $E$ and is Borel, being the intersection of countably many Borel tests.
    To construct its analytic presentation at the fixed parameter, put
    $$\begin{aligned}
    B_e&:=\{(u,v):u\in D_e,\ v\in D'_e,\ u\mathrel E v\},\\
    J_e&:=\{p:e\notin C\},\qquad K_e:=\{p:B_e\ne\emptyset\},\\
    L_e&:=(D'_e\times X\ \cup\ X\times D_e)
           \cap(X\times D'_e\ \cup\ D_e\times X).
    \end{aligned}$$
    For valid $e$, nonemptiness of $B_e$ is exactly failure of invariance of $D_e$. One implication follows
    from a pair leaving $D_e$; for the other, symmetry of $E$ turns either direction of failed invariance
    into such a pair. Also, membership of $(x,y)$ in $L_e$ says exactly that both points agree on membership
    in $D_e$. Consequently the graph is
    $$\EffectiveClosureER{E}=\bigcap_e(J_e\cup K_e\cup L_e),$$
    where pairs are coded as points of Baire space. Each family on the right has a joint tree decider:
    use coordinate inverse images, intersections, and the nonemptiness operation for $B_e,K_e$, and
    binary unions and intersections for $L_e$. Invalidity is handled by $J_e$. Uniform countable
    intersection therefore gives an analytic presentation of the actual invariant-test relation, without
    a procedure selecting the valid invariant codes.
-/
theorem projected_invariantSetoid (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r) :
    ProjectedRelation ε (invariantSetoid ε E).r := by
  classical
  obtain ⟨C⟩ := exists_complementedCodes ε
  let bad := fun n => {p | leftBaire p ∈ C.positiveSet n} ∩
    {p | rightBaire p ∈ C.negativeSet n} ∩ {p | E.r (leftBaire p) (rightBaire p)}
  have hb : UniformProjected ε bad :=
    (C.uniform_positive.left.inter C.uniform_negative.right).inter (.const hE)
  have hbad (n : ℕ) (hv : ValidComplementedIndex ε n) :
      (bad n).Nonempty ↔ ¬ ERInvariant E (C.positiveSet n) := by
    have hc (x : ℕ → ℕ) : x ∈ C.negativeSet n ↔ x ∉ C.positiveSet n := by
      simp only [C.complementary hv, mem_compl_iff, not_not]
    constructor
    · rintro ⟨p, ⟨hl, hr⟩, hrel⟩ hi
      exact (hc _).mp hr ((hi hrel).mp hl)
    · intro hn
      by_contra hnone
      apply hn
      intro x y hxy
      constructor
      · intro hx
        by_contra hy
        apply hnone
        exact ⟨pairBaire x y, by simpa [bad] using And.intro (And.intro hx ((hc y).mpr hy)) hxy⟩
      · intro hy
        by_contra hx
        apply hnone
        exact ⟨pairBaire y x, by simpa [bad] using And.intro (And.intro hy ((hc x).mpr hx)) (E.symm hxy)⟩
  let agree := fun n => ({p | leftBaire p ∈ C.negativeSet n} ∪
      {p | rightBaire p ∈ C.positiveSet n}) ∩
    ({p | rightBaire p ∈ C.negativeSet n} ∪ {p | leftBaire p ∈ C.positiveSet n})
  have ha : UniformProjected ε agree :=
    (C.uniform_negative.left.union C.uniform_positive.right).inter
      (C.uniform_negative.right.union C.uniform_positive.left)
  have hagree (n : ℕ) (hv : ValidComplementedIndex ε n) (p : ℕ → ℕ) :
      p ∈ agree n ↔ (leftBaire p ∈ C.positiveSet n ↔ rightBaire p ∈ C.positiveSet n) := by
    simp only [agree, mem_inter_iff, mem_union, mem_ofPred_eq, C.complementary hv, mem_compl_iff]
    tauto
  have h := ((uniform_invalidComplementedIndex ε).union hb.nonempty).union ha
  have heq : (⋂ n, ({_p | ¬ ValidComplementedIndex ε n} ∪
      {_p | (bad n).Nonempty}) ∪ agree n) =
      {p | (invariantSetoid ε E).r (leftBaire p) (rightBaire p)} := by
    ext p
    simp only [mem_iInter, mem_union, mem_ofPred_eq]
    change (∀ n, (¬ ValidComplementedIndex ε n ∨ (bad n).Nonempty) ∨ p ∈ agree n) ↔
      ∀ D, Complemented ε D → ERInvariant E D →
        (leftBaire p ∈ D ↔ rightBaire p ∈ D)
    constructor
    · intro hp D hc hi
      obtain ⟨n, hn, rfl⟩ := C.complete hc
      apply (hagree n hn p).mp
      exact (hp n).resolve_left (by rw [hbad n hn]; tauto)
    · intro hp n
      by_cases hv : ValidComplementedIndex ε n
      · by_cases hi : ERInvariant E (C.positiveSet n)
        · exact Or.inr ((hagree n hv p).mpr (hp _ (C.sound hv) hi))
        · exact Or.inl (Or.inr ((hbad n hv).mpr hi))
      · exact Or.inl (Or.inl hv)
  change Projected ε {p | (invariantSetoid ε E).r (leftBaire p) (rightBaire p)}
  exact heq ▸ h.iInter

/-- The HKL gap kernel has a code in the same parameter as the Borel relation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    In the kernel arguments, invalidity and failures of homogeneity or invariance will enter as analytic
    alternatives, uniformly in the code. This interface uses separation directly and does not require a
    completeness theorem for a separate Borel-expression syntax.
-/
theorem projected_hklKernel (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y)) :
    Projected ε (equivalenceGapKernel E (invariantSetoid ε E)) :=
  projected_invariantKernel ε E hneE (projected_invariantSetoid ε E hE)

/-- Hereditary failure for the actual auxiliary relation, with its relative
analyticity now proved from E rather than assumed. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Hereditary failure of separation
-/
theorem hkl_hereditary (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    {A : Set (ℕ → ℕ)} (hA : Projected ε A)
    (hne : A.Nonempty) (hAH : A ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ x ∈ A, ∃ y ∈ A, (invariantSetoid ε E).r x y ∧ ¬ E.r x y :=
  hkl_hereditary_failure ε E hE hneE (projected_invariantSetoid ε E hE) hA hne hAH

end LambdaTree
end PolishSpaceBook
