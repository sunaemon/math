module

public import PolishSpaceBook.CategoryLocalization
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! # Borel category quantifiers

The proof is simultaneous induction on the Borel construction, with the
open parameter set universally quantified throughout the induction.
-/
namespace PolishSpaceBook
open Set Topology TopologicalSpace

/-- Nonmeager and comeager section quantifiers preserve Borel sets. -/
theorem measurable_category_quantifiers_polish
    {G X : Type*} [TopologicalSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {R : Set (G × X)} (hR : MeasurableSet R) :
    ∀ U : Set G, IsOpen U →
      MeasurableSet (categoryStar U R) ∧ MeasurableSet (categoryTriangle U R) := by
  induction R, hR using MeasurableSet.induction_on_open with
  | isOpen R hR =>
    intro U hU
    exact ⟨(isOpen_categoryStar hU hR).measurableSet,
      (isGdelta_categoryTriangle_open (isBasis_countableBasis G)
        (countable_countableBasis G) hU hR).measurableSet⟩
  | compl R _ ih =>
    intro U hU
    rw [← categoryTriangle_compl, ← categoryStar_compl]
    exact ⟨(ih U hU).2.compl, (ih U hU).1.compl⟩
  | iUnion R _ hR ih =>
    intro U hU
    constructor
    · rw [categoryStar_iUnion]
      exact MeasurableSet.iUnion fun n => (ih n U hU).1
    · have hb : ∀ n x, BaireMeasurableSet (relationSection (R n) x) := by
        intro n x
        exact ((hR n).preimage (measurable_id.prodMk measurable_const)).baireMeasurableSet
      rw [categoryTriangle_iUnion (isBasis_countableBasis G) hU R hb]
      apply MeasurableSet.biInter (countable_countableBasis G)
      intro V hVB
      exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        MeasurableSet.iUnion fun n => (ih n V (isOpen_of_mem_countableBasis hVB)).1

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose a Polish topology presenting the standard Borel structure of $X$. Prove both assertions simultaneously for
    all open $U$ by induction on the Borel construction of $R$. For open $R$, every section $R_x\cap U$ is open.
    Its non-meagerness is equivalent to nonemptiness, an open condition on $x$; its comeagerness is equivalent to meeting
    every nonempty basic $W\IncludedIn U$, a countable intersection of open conditions.

    Complements exchange the two category quantifiers, so the induction hypothesis passes to complements.
    For $R=\bigcup_n R_n$, the non-meager quantifier is the countable union of the corresponding quantifiers for $R_n$.
    For the comeager quantifier, use the localized union rule: take the intersection over nonempty basic
    $W\IncludedIn U$ of the union of the non-meager quantifiers for $R_n$ on $W$.
    Each section is Borel and hence has the Baire property, as required for that rule. The induction hypothesis applies
    to every such $W$, and the basis is countable, so this is again a Borel set.
    This completes the Montgomery--Novikov category-quantifier argument.
    \end{proof}
-/
/-- A standard Borel parameter space is handled by choosing a compatible Polish topology. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  kind: lemma
  title: Borel category quantifiers
-/
theorem measurable_category_quantifiers
    {G X : Type*} [TopologicalSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace X] [StandardBorelSpace X]
    {R : Set (G × X)} (hR : MeasurableSet R) (U : Set G) (hU : IsOpen U) :
    MeasurableSet (categoryStar U R) ∧ MeasurableSet (categoryTriangle U R) := by
  let := upgradeStandardBorel X
  exact measurable_category_quantifiers_polish hR U hU

end PolishSpaceBook
