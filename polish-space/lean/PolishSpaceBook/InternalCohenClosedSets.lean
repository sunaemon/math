module

public import PolishSpaceBook.InternalCohenAvoidance
public import PolishSpaceBook.InternalCohenBorelCodes

@[expose] public section

/-! # Borel representatives of the model's closed nowhere-dense sets

Closedness is expressed in the cylinder basis: every point outside A has a
finite prefix with no extension in A. Together with the bounded nowhere-density
test, this constructs a dense word family and a code for its closed complement.
-/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure
universe u

/-- Parameters finite binary words, binary points, and the proposed closed set. -/
def cohenClosedPredicate : BoundedSetPredicate 3 :=
  .conj (.subset 2 1) (.all 1 (.disj (.member 3 2)
    (.ex 0 (.conj (.subset 4 3) (.all 2 (.neg (.subset 4 5)))))))

lemma eval_cohenClosedPredicate (M A : ZFSet.{u}) :
    cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, A] ↔
      A ⊆ internalCantor M ∧ ∀ x : ℕ → Bool, cantorPointGraph x ∈ M →
        cantorPointGraph x ∉ A → ∃ s ∈ cohenAvoidanceSet A, x ∈ cyl s := by
  simp only [cohenClosedPredicate, eval, Fin.snoc, or_iff_not_imp_left]
  change (A ⊆ internalCantor M ∧ ∀ g ∈ internalCantor M, g ∉ A →
    ∃ s ∈ cohenConditionSet Set.univ, s ⊆ g ∧ ∀ h ∈ A, ¬ s ⊆ h) ↔ _
  apply and_congr_right
  intro _
  constructor
  · intro h x hxM hxA
    obtain ⟨s, hs, hsg, hsh⟩ := h _ ((BorelExpression.cantorPointGraph_mem_internalCantor (M := M) x).mpr hxM) hxA
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hs
    exact ⟨s, hsh, (binaryWordGraph_subset_pointGraph s x).mp hsg⟩
  · intro h g hg hgA
    obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp hg
    obtain ⟨s, hs, hxs⟩ := h x hxM hgA
    exact ⟨wordGraph (s.map Bool.toNat), mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩,
      (binaryWordGraph_subset_pointGraph s x).mpr hxs, hs⟩

/-- An externally closed interpretation satisfies the model's basis test. -/
lemma cohenClosedPredicate_of_closed (M : ZFSet.{u}) (c : Code) (hc : IsClosed c.cantor) :
    cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M,
      internalBorelCantorSet M c.val c.property.2.2.2.2.2] := by
  apply (eval_cohenClosedPredicate M _).mpr
  refine ⟨fun _ hg => (ZFSet.mem_inter.mp hg).2, ?_⟩
  intro x hxM hxA
  have hx : x ∈ c.cantorᶜ := by
    intro hxc
    exact hxA ((cantorPointGraph_mem_internalBorelCantorSet M c.val _ x).mpr ⟨hxM, hxc⟩)
  obtain ⟨s, hxs, hs⟩ := exists_cyl_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨s, ?_, hxs⟩
  rw [cohenAvoidanceSet_interpretation]
  exact fun y _ hy => hs hy

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Internal avoiding conditions
-/
include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Bounded separation on $P$ constructs $D_A$ in $M$. Transitivity makes $N(A)$ absolute, so this same family
    is dense externally. The preceding construction gives an internal code for the closed nowhere-dense set
    $\SetDifference{\CantorSpace}{U_{D_A}}$.
    A point of $A$ has no prefix in $D_A$. Conversely, $C(A)$ gives every internal point outside $A$ a prefix in
    $D_A$. Thus this code has internal interpretation exactly $A$.
    For an arbitrary code $a$ with that internal interpretation, membership in $D_A$ means that the cylinder
    contains no internal point of $\BorelValue{a}$. Apply Borel-inclusion transfer to the cylinder code
    and the complement code of $a$, as in the preceding cover lemma.
    The cylinder is disjoint from the full external interpretation as well.
    The reverse implication follows by restriction to internal points.
-/
/-- This derives the code's existence from the model's closed-set witness. -/
theorem exists_internal_code_of_closed_nowhereDense (A : ZFSet.{u}) (hA : A ∈ M)
    (hclosed : cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, A])
    (hnd : cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, A]) :
    ∃ c : Code, c.val.labelGraph ∈ M ∧
      internalBorelCantorSet M c.val c.property.2.2.2.2.2 = A ∧
      IsClosed c.cantor ∧ IsNowhereDense c.cantor := by
  let D := cohenAvoidanceSet A
  have hd := (eval_cohenNowhereDensePredicate_set A).mp hnd
  obtain ⟨c, hcM, hcD, hcclosed, hcnd⟩ := exists_internal_closedCode_of_cohenDense
    hM hinf hpair hunion hpower hsep hrep D
    (cohenAvoidanceSet_mem hM hinf hpair hunion hpower hsep A hA) hd
  obtain ⟨hAY, hclosed⟩ := (eval_cohenClosedPredicate M A).mp hclosed
  refine ⟨c, hcM, ?_, hcclosed, hcnd⟩
  ext g
  constructor
  · intro hg
    obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
    obtain ⟨hxM, hxc⟩ := (cantorPointGraph_mem_internalBorelCantorSet M c.val _ x).mp hg
    by_contra hxA
    obtain ⟨s, hs, hxs⟩ := hclosed x hxM hxA
    change x ∈ c.cantor at hxc
    rw [hcD] at hxc
    exact hxc (mem_cylinderCode.mpr ⟨s, hs, hxs⟩)
  · intro hg
    obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp (hAY hg)
    apply (cantorPointGraph_mem_internalBorelCantorSet M c.val _ x).mpr
    refine ⟨hxM, ?_⟩
    change x ∈ c.cantor
    rw [hcD]
    intro hx
    obtain ⟨s, hs, hxs⟩ := mem_cylinderCode.mp hx
    exact hs _ hg ((binaryWordGraph_subset_pointGraph s x).mpr hxs)

include hM hinf hpair hunion hpower hsep hrep hchoice in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Suppose first that $c$ is Cohen-generic, and let $a\in M$ code a set that the model judges to be meager.
    Choose an internal closed nowhere-dense cover $\Sequence{A_n}{n\in\omega}$ using the preceding witness lemma.
    The avoiding-condition lemma constructs each dense family $D_{A_n}$ inside $M$.
    Genericity gives a prefix of $c$ in each such family, so $c$ avoids the external interpretation of every cover member.
    The same lemma supplies an internal Borel code for each $A_n$.
    Use §{sec:internal-borel-code-recognition} to choose the whole sequence of their codes inside $M$.
    The Borel-cover transfer makes the internal covering inclusion valid at $c$ as well.
    Thus $c\notin\BorelValue{a}$.
-/
/-- A meager-cover witness supplies its own internal Borel representatives. -/
theorem cohenGeneric_avoids_meager_witness (x : ℕ → Bool)
    (hg : ∀ D : Set CohenCondition, cohenConditionSet D ∈ M → CohenDense D →
      ∃ s ∈ D, x ∈ cyl s)
    (c : Code) (hc : c.val.labelGraph ∈ M)
    (V : ℕ → ZFSet.{u}) (hV : sequenceGraph V ∈ M)
    (hclosed : ∀ n, cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, V n])
    (hnd : ∀ n, cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, V n])
    (hcover : internalBorelCantorSet M c.val c.property.2.2.2.2.2 ⊆ sequenceUnion V) :
    x ∉ c.cantor := by
  apply cohenGeneric_avoids_internal_cover hM hinf hpair hunion hpower hsep hrep hchoice x hg c hc V hV
    ?_ hnd hcover
  intro n
  obtain ⟨d, hdM, hdV, _, _⟩ := exists_internal_code_of_closed_nowhereDense hM hinf hpair hunion hpower hsep hrep
    (V n) (sequence_term_mem hM hunion V hV n) (hclosed n) (hnd n)
  exact ⟨d.val, d.property, hdM, hdV⟩

end PolishSpaceBook
