module

public import PolishSpaceBook.LambdaKernelConditions

@[expose] public section

/-!
# Disjoint compatible refinements in the actual HKL kernel

The absence of a distinct E-related pair forces equality of the two sets
and makes E equality there. Separate the saturations of disjoint cylinder
pieces by the proved relative invariant separation theorem. This contradicts
the hereditary failure of equality with the actual invariant-test relation.
All refinements have lambda presentations in the original parameter.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    First there are distinct $a\in A,b\in B$ with $a\mathrel E b$. Otherwise equality of saturations forces $A=B$ and
    makes $E$ equality on $A$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Hereditary failure gives $x,y\in A$ with
    $x\mathrel{\EffectiveClosureER{E}}y$ and $x\mathrel{\not E}y$. In particular they are distinct. Choose disjoint
    clopen cylinders $U,V$ containing them. The saturations of $A\cap U$ and $A\cap V$ are disjoint:
    a common point would give two $E$-equivalent points of $A$ in disjoint cylinders, contradicting equality on
    $A$. Invariant separation supplies an invariant $\lDelta^1_1$ set containing the first saturation and
    avoiding the second. It separates $x,y$, contrary to the definition of $\EffectiveClosureER{E}$.
-/
/-- The kernel supplies the distinct E-related pair used in rectangular
splitting. The cylinder at y is chosen inside the complement of the cylinder
at x; this smaller piece suffices for the book's invariant-separation step. -/
theorem hkl_distinct_related (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    {A B : Set FusionReal} (hA : Projected ε A)
    (hAn : A.Nonempty) (hAH : A ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    (hAB : erSaturation E A = erSaturation E B) :
    ∃ a ∈ A, ∃ b ∈ B, E.r a b ∧ a ≠ b := by
  classical
  by_contra hn
  have hid {a b : FusionReal} (ha : a ∈ A) (hb : b ∈ B) (hab : E.r a b) : a = b := by
    by_contra hne
    exact hn ⟨a, ha, b, hb, hab, hne⟩
  have heq : A = B := by
    apply Subset.antisymm
    · intro a ha
      have hs := subset_erSaturation E A ha
      rw [hAB] at hs
      obtain ⟨b, hb, hba⟩ := hs
      exact (hid ha hb (E.symm hba)) ▸ hb
    · intro b hb
      have hs := subset_erSaturation E B hb
      rw [← hAB] at hs
      obtain ⟨a, ha, hab⟩ := hs
      exact (hid ha hb hab) ▸ ha
  have hdiag {a b : FusionReal} (ha : a ∈ A) (hb : b ∈ A) (hab : E.r a b) : a = b :=
    hid ha (heq ▸ hb) hab
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hkl_hereditary ε E hE hneE hA hAn hAH
  have hne' : x ≠ y := fun he => hne (he ▸ E.refl x)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne'
  obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open hxU hU
  obtain ⟨t, hyt, htV⟩ := exists_cyl_subset_of_mem_open hyV hV
  have hst : Disjoint (cyl s) (cyl t) := hUV.mono hsU htV
  have hs : Projected ε (A ∩ cyl s) :=
    hA.inter (projected_cyl ε s)
  have ht : Projected ε (A ∩ cyl t) :=
    hA.inter (projected_cyl ε t)
  have hd : Disjoint (erSaturation E (A ∩ cyl s)) (erSaturation E (A ∩ cyl t)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
    have hab := hdiag ha.1 hb.1 (E.trans haz (E.symm hbz))
    exact Set.disjoint_left.mp hst (hab ▸ ha.2) hb.2
  obtain ⟨C, hC, hCi, hsC, hCt⟩ := invariant_separation ε E hE
    (projected_erSaturation E hE hs) (projected_erSaturation E hE ht)
    hd (erSaturation_invariant E _)
  have hxC := hsC (subset_erSaturation E _ ⟨hx, hxs⟩)
  have hyC := (hxy C hC hCi).mp hxC
  exact Set.disjoint_left.mp hCt hyC (subset_erSaturation E _ ⟨hy, hyt⟩)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Choose disjoint clopen neighborhoods $U,V$ of such $a,b$ and put
    $$A_0=A\cap U,\qquad B_0=B\cap V,\qquad
    A'=A_0\cap\ERSaturation{B_0}{E},\qquad
    B'=B_0\cap\ERSaturation{A_0}{E}.$$
    Both sets are nonempty and analytic. Their saturations both equal
    $\ERSaturation{A_0}{E}\cap\ERSaturation{B_0}{E}$, and they are disjoint.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Disjoint compatible refinements
-/
/-- Intersect disjoint cylinder pieces with each other's saturation. The
resulting relative analytic sets have the same saturation and are nonempty. -/
theorem disjoint_compatible_refinement (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    {A B : Set FusionReal} (hA : Projected ε A)
    (hB : Projected ε B)
    (hAn : A.Nonempty) (hAH : A ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    (hAB : erSaturation E A = erSaturation E B) :
    ∃ A' B', Projected ε A' ∧
      Projected ε B' ∧ A'.Nonempty ∧ B'.Nonempty ∧
      A' ⊆ A ∧ B' ⊆ B ∧ Disjoint A' B' ∧ erSaturation E A' = erSaturation E B' := by
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hkl_distinct_related ε E hE hneE hA hAn hAH hAB
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hne
  obtain ⟨s, has, hsU⟩ := exists_cyl_subset_of_mem_open haU hU
  obtain ⟨t, hbt, htV⟩ := exists_cyl_subset_of_mem_open hbV hV
  let A₀ := A ∩ cyl s
  let B₀ := B ∩ cyl t
  have hA₀ : Projected ε A₀ :=
    hA.inter (projected_cyl ε s)
  have hB₀ : Projected ε B₀ :=
    hB.inter (projected_cyl ε t)
  refine ⟨A₀ ∩ erSaturation E B₀, B₀ ∩ erSaturation E A₀,
    hA₀.inter (projected_erSaturation E hE hB₀),
    hB₀.inter (projected_erSaturation E hE hA₀),
    ⟨a, ⟨ha, has⟩, b, ⟨hb, hbt⟩, E.symm hab⟩,
    ⟨b, ⟨hb, hbt⟩, a, ⟨ha, has⟩, hab⟩,
    fun _ h => h.1.1, fun _ h => h.1.1, ?_, ?_⟩
  · exact (hUV.mono hsU htV).mono (fun _ h => h.1.2) (fun _ h => h.1.2)
  · rw [erSaturation_inter_saturation, erSaturation_inter_saturation, inter_comm]

/-- The restricted product uses only conditions in the fixed-parameter catalog. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Let $\RestrictedGHProduct{E}$ consist of rectangles $A\times B$ with $A,B\in\GHConditions{1}$ and
    $\ERSaturation{A}{E}=\ERSaturation{B}{E}$, again ordered by inclusion.
-/
abbrev ParameterCompatibleRectangle (ε : ℕ → ℕ) (E : Setoid FusionReal) :=
  {p : (parameterAnalyticCatalog ε).Condition × (parameterAnalyticCatalog ε).Condition //
    erSaturation E p.1.val.val = erSaturation E p.2.val.val}

namespace ParameterCompatibleRectangle
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}

/-- Restore compatibility after an arbitrary permitted shrink of the left
coordinate, retaining exactly the requested left condition. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If $A'$ is a nonempty analytic subset of
    $A$, replace $B$ by $B\cap\ERSaturation{A'}{E}$. This is nonempty and restores equality of saturations.
-/
theorem refine_left (P : ParameterCompatibleRectangle ε E)
    (hE : ProjectedRelation ε E.r)
    (A : (parameterAnalyticCatalog ε).Condition) (hA : A ≤ P.val.1) :
    ∃ Q : ParameterCompatibleRectangle ε E, Q ≤ P ∧ Q.val.1 = A := by
  let B := P.val.2.val.val ∩ erSaturation E A.val.val
  have hn : B.Nonempty := by
    obtain ⟨x, hx⟩ := A.val.property.2
    have hs := subset_erSaturation E _ (hA hx)
    rw [P.property] at hs
    obtain ⟨y, hy, hyx⟩ := hs
    exact ⟨y, hy, x, hx, E.symm hyx⟩
  let C := parameterCondition ε B ((parameterCondition_projected ε P.val.2).inter
    (projected_erSaturation E hE (parameterCondition_projected ε A))) hn
  have hc : erSaturation E A.val.val = erSaturation E C.val.val := by
    change _ = erSaturation E (P.val.2.val.val ∩ erSaturation E A.val.val)
    rw [erSaturation_inter_saturation]
    symm
    apply inter_eq_right.mpr
    rw [← P.property]
    exact erSaturation_mono E hA
  exact ⟨⟨(A, C), hc⟩, ⟨hA, inter_subset_left⟩, rfl⟩

/-- Every rectangle below the actual kernel admits a disjoint compatible
refinement; there is no distinct-related-pair hypothesis in this API. -/
theorem disjoint_refinement (P : ParameterCompatibleRectangle ε E)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hPH : P.val.1.val.val ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ Q : ParameterCompatibleRectangle ε E, Q ≤ P ∧ Disjoint Q.val.1.val.val Q.val.2.val.val := by
  obtain ⟨A, B, hA, hB, hnA, hnB, hsA, hsB, hd, hc⟩ :=
    disjoint_compatible_refinement ε E hE hneE
      (parameterCondition_projected ε P.val.1) (parameterCondition_projected ε P.val.2)
      P.val.1.val.property.2 hPH P.property
  exact ⟨⟨(parameterCondition ε A hA hnA, parameterCondition ε B hB hnB), hc⟩,
    ⟨hsA, hsB⟩, hd⟩

end ParameterCompatibleRectangle
end LambdaTree
end PolishSpaceBook
