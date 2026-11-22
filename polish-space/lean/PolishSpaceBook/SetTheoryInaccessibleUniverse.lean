module

public import PolishSpaceBook.SetTheoryUniverseInaccessible

@[expose] public section

/-! # An inaccessible rank stage is a Grothendieck universe

The size bound is proved by induction on stages: power sets at successors,
and regularity at limits. It then bounds the ranks in each indexed union.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open Order
universe u

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] \emph{$(\Leftarrow)$} First note the size bound: if $\kappa$ is inaccessible and
    $\alpha<\kappa$, then $|V_\alpha|<\kappa$. Induct on $\alpha$. The zero stage is empty; a successor stage is a
    power set, so the strong-limit property applies. At a limit stage, regularity bounds the union of fewer than
    $\kappa$ sets of cardinality less than $\kappa$. Every $x\in V_\kappa$ is a subset of a stage below $\kappa$,
    so $|x|<\kappa$ as well.
-/
lemma card_vonNeumann_lt_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {α : Ordinal.{u}} (hα : α < κ.ord) : (ZFSet.vonNeumann α).card < κ := by
  rw [ZFSet.card_vonNeumann]
  induction α using Ordinal.limitRecOn with
  | zero => simpa only [Cardinal.preBeth_zero] using hκ.pos
  | add_one α ih =>
    rw [Cardinal.preBeth_add_one]
    exact hκ.isStrongPrelimit (ih ((Order.lt_succ α).trans hα))
  | limit α hlim ih =>
    rw [Cardinal.preBeth_limit hlim.isSuccPrelimit]
    apply Cardinal.lift_iSup_lt_of_lt_cof_ord
    · rwa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, hκ.isRegular.lift.cof_ord,
        Cardinal.lift_lt, ← Cardinal.lt_ord]
    · intro β
      exact ih β.val β.property (β.property.trans hα)

lemma card_mem_vonNeumann_lt_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {x : ZFSet.{u}} (hx : x ∈ ZFSet.vonNeumann κ.ord) : x.card < κ :=
  (ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)).trans_lt
    (card_vonNeumann_lt_inaccessible hκ (ZFSet.mem_vonNeumann.mp hx))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    The set $V_\kappa$ is transitive. Pairing and power-set closure follow from the rank formulas
    $$\mathrm{rk}(\{x,y\})=\max\{\mathrm{rk}(x)+1,\mathrm{rk}(y)+1\},\qquad
    \mathrm{rk}(\PowerSet{x})=\mathrm{rk}(x)+1$$
    and the fact that $\kappa$ is a limit ordinal. Also $\omega\in V_\kappa$, since $\omega<\kappa$.
    For indexed unions, let $I\in V_\kappa$ and $f:I\to V_\kappa$. The size bound gives $|I|<\kappa$;
    regularity then gives
    $$\mathrm{rk}\left(\bigcup_{i\in I}f(i)\right)
    =\sup_{i\in I}\mathrm{rk}(f(i))<\kappa.$$
    Thus the indexed union belongs to $V_\kappa$.
-/
theorem inaccessible_vonNeumann_isGrothendieckUniverse {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsGrothendieckUniverse (ZFSet.vonNeumann κ.ord) := by
  have hlim := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  refine ⟨ZFSet.isTransitive_vonNeumann _, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_pair]
    exact max_lt (hlim.succ_lt (ZFSet.mem_vonNeumann.mp hx))
      (hlim.succ_lt (ZFSet.mem_vonNeumann.mp hy))
  · intro x hx
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    exact hlim.succ_lt (ZFSet.mem_vonNeumann.mp hx)
  · intro I hI f hf
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_iUnion]
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Cardinal.lift_ord,
        hκ.isRegular.lift.cof_ord, Cardinal.lift_lt]
      exact card_mem_vonNeumann_lt_inaccessible hκ hI
    · intro i
      exact ZFSet.mem_vonNeumann.mp (hf i)
  · rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hκ.aleph0_lt

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: Grothendieck
-/
theorem grothendieck_universe_iff (U : ZFSet.{u}) :
    IsGrothendieckUniverse U ↔ ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ U = ZFSet.vonNeumann κ.ord := by
  constructor
  · exact IsGrothendieckUniverse.exists_inaccessible_stage
  · rintro ⟨κ, hκ, rfl⟩
    exact inaccessible_vonNeumann_isGrothendieckUniverse hκ

end PolishSpaceBook.SetTheoryModels
