module

public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-! # Grothendieck universes and their ordinal height

The closure axioms are the ones used in the book. Rank closure and hierarchy
closure are proved explicitly before identifying the universe with a rank stage.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open Order
universe u

/-- The standard universe axioms, including infinity. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Grothendieck universes.** A \termdefine{Grothendieck universe} is a set $U$ satisfying:
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Transitivity.** $x \in y \in U$ implies $x \in U$.
    *   **Pairing.** $x, y \in U$ implies $\{x, y\} \in U$.
    *   **Power Set.** $x \in U$ implies $\PowerSet{x} \in U$.
    *   **Indexed union.** If $I \in U$ and $f : I \to U$ is a function, then $\bigcup_{i \in I} f(i) \in U$.
    *   **Infinity.** $\omega \in U$.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a Grothendieck universe $U$ with $\omega \in U$, in the sense of §{sec:inaccessible-universes}. The size conventions
    for the rest of this appendix are:
-/
structure IsGrothendieckUniverse (U : ZFSet.{u}) : Prop where
  transitive : U.IsTransitive
  pair_mem : ∀ ⦃x y⦄, x ∈ U → y ∈ U → ({x, y} : ZFSet.{u}) ∈ U
  powerset_mem : ∀ ⦃x⦄, x ∈ U → ZFSet.powerset x ∈ U
  indexedUnion_mem : ∀ ⦃I : ZFSet.{u}⦄, I ∈ U → ∀ f : I → ZFSet.{u},
    (∀ i, f i ∈ U) → ZFSet.iUnion f ∈ U
  omega_mem : Ordinal.omega0.toZFSet ∈ U

namespace IsGrothendieckUniverse
variable {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

lemma subset_mem {x y : ZFSet.{u}} (hy : y ∈ U) (hxy : x ⊆ y) : x ∈ U :=
  hU.transitive.mem_trans (ZFSet.mem_powerset.mpr hxy) (hU.powerset_mem hy)

lemma singleton_mem {x : ZFSet.{u}} (hx : x ∈ U) : ({x} : ZFSet.{u}) ∈ U := by
  simpa only [ZFSet.pair_eq_singleton] using hU.pair_mem hx hx

lemma sUnion_mem {x : ZFSet.{u}} (hx : x ∈ U) : ZFSet.sUnion x ∈ U := by
  have h := hU.indexedUnion_mem hx (fun y : x => y.val)
    (fun y => hU.transitive.mem_trans y.property hx)
  have he : ZFSet.iUnion (fun y : x => y.val) = ZFSet.sUnion x := by
    ext z
    simp only [ZFSet.mem_iUnion, ZFSet.mem_sUnion]
    exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩, fun ⟨y, hy, hz⟩ => ⟨⟨y, hy⟩, hz⟩⟩
  exact he ▸ h

lemma union_mem {x y : ZFSet.{u}} (hx : x ∈ U) (hy : y ∈ U) : x ∪ y ∈ U := by
  simpa only [ZFSet.sUnion_pair] using hU.sUnion_mem (hU.pair_mem hx hy)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \emph{$(\Rightarrow)$} Let $\kappa:=U\cap\mathrm{Ord}$. Transitivity makes this an ordinal, and
    $\omega\in U$ gives $\omega<\kappa$. Pairing and indexed unions give closure under singletons and binary
    unions. Hence $\alpha\in U$ implies $\alpha+1=\alpha\cup\{\alpha\}\in U$ for ordinals, so $\kappa$ is a limit.
    Indexed-union closure also gives
    $$\sup_{i\in I}\alpha_i=\bigcup_{i\in I}\alpha_i\in U\cap\mathrm{Ord}=\kappa
    \qquad(I\in U,\ \alpha_i<\kappa).$$
-/
lemma ordinal_succ_mem {α : Ordinal.{u}} (hα : α.toZFSet ∈ U) : (α + 1).toZFSet ∈ U := by
  rw [Ordinal.toZFSet_add_one]
  have he : insert α.toZFSet α.toZFSet = ({α.toZFSet} : ZFSet.{u}) ∪ α.toZFSet := by
    ext z
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_union, ZFSet.mem_singleton]
  rw [he]
  exact hU.union_mem (hU.singleton_mem hα) hα

omit hU in
/-- The usual rank recurrence, with ordinal values viewed as sets. -/
lemma rank_eq_union_predecessor_ranks (x : ZFSet.{u}) :
    x.rank.toZFSet = ZFSet.iUnion (fun y : x => (y.val.rank + 1).toZFSet) := by
  ext z
  constructor
  · intro hz
    obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    obtain ⟨y, hy, hβy⟩ := ZFSet.lt_rank_iff.mp hβ
    exact ZFSet.mem_iUnion.mpr ⟨⟨y, hy⟩, Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (lt_of_le_of_lt hβy (Order.lt_succ _))⟩
  · intro hz
    obtain ⟨y, hy⟩ := ZFSet.mem_iUnion.mp hz
    obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
    apply Ordinal.toZFSet_mem_toZFSet_iff.mpr
    exact (Order.lt_succ_iff.mp hβ).trans_lt (ZFSet.rank_lt_of_mem y.property)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    For $x\in U$, induction on membership gives $\mathrm{rk}(x)\in U$.
    Indeed, each $y\in x$ belongs to $U$ by transitivity, so the induction hypothesis and successor closure give
    $\mathrm{rk}(y)+1\in U$. Apply indexed-union closure over the index set $x$ to obtain
    $$\mathrm{rk}(x)=\bigcup_{y\in x}\bigl(\mathrm{rk}(y)+1\bigr)\in U\cap\mathrm{Ord}=\kappa.$$
    Thus $U\IncludedIn V_\kappa$.
-/
lemma rank_mem {x : ZFSet.{u}} (hx : x ∈ U) : x.rank.toZFSet ∈ U := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [rank_eq_union_predecessor_ranks]
    exact hU.indexedUnion_mem hx _ (fun y => hU.ordinal_succ_mem
      (ih y.val y.property (hU.transitive.mem_trans y.property hx)))

omit hU in
/-- The hierarchy recurrence indexed by the actual elements of an ordinal set. -/
lemma vonNeumann_eq_ordinal_union (α : Ordinal.{u}) :
    ZFSet.vonNeumann α =
      ZFSet.iUnion (fun β : α.toZFSet => ZFSet.powerset (ZFSet.vonNeumann β.val.rank)) := by
  ext z
  rw [ZFSet.mem_vonNeumann', ZFSet.mem_iUnion]
  constructor
  · rintro ⟨β, hβ, hz⟩
    refine ⟨⟨β.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ⟩, ?_⟩
    simpa only [Ordinal.rank_toZFSet, ZFSet.mem_powerset] using hz
  · rintro ⟨β, hz⟩
    refine ⟨β.val.rank, ?_, ZFSet.mem_powerset.mp hz⟩
    simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem β.property

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Conversely, transfinite induction gives $V_\alpha\in U$ for every $\alpha<\kappa$.
    The zero, successor, and limit recursions can be written together as
    $$V_\alpha=\bigcup_{\beta<\alpha}\PowerSet{V_\beta}.$$
    The index set $\alpha$ belongs to $U$, and the induction hypothesis followed by power-set closure puts each
    term of this union in $U$. Now if $x\in V_\kappa$, its rank and the successor of its rank are below $\kappa$.
    Hence $V_{\mathrm{rk}(x)+1}\in U$; since $x\in V_{\mathrm{rk}(x)+1}$, transitivity gives $x\in U$.
    Therefore $U=V_\kappa$.
-/
lemma vonNeumann_mem {α : Ordinal.{u}} (hα : α.toZFSet ∈ U) : ZFSet.vonNeumann α ∈ U := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    rw [vonNeumann_eq_ordinal_union]
    apply hU.indexedUnion_mem hα
    intro β
    apply hU.powerset_mem
    apply ih β.val.rank
    · simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem β.property
    · have hord := (ZFSet.isOrdinal_toZFSet α).mem β.property
      rw [hord.toZFSet_rank_eq]
      exact hU.transitive.mem_trans β.property hα

/-- The ordinal height is exactly the ordinal formed by the ordinals in the universe. -/
def ordinalPart (U : ZFSet.{u}) : ZFSet.{u} := U.sep ZFSet.IsOrdinal

def height (U : ZFSet.{u}) : Ordinal.{u} := (ordinalPart U).rank

lemma ordinalPart_isOrdinal : (ordinalPart U).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨hxU, hxord⟩ := ZFSet.mem_sep.mp hx
    exact ZFSet.mem_sep.mpr ⟨hU.transitive.mem_trans hy hxU, hxord.mem hy⟩
  · intro x hx
    exact (ZFSet.mem_sep.mp hx).2

lemma height_toZFSet : (height U).toZFSet = ordinalPart U :=
  hU.ordinalPart_isOrdinal.toZFSet_rank_eq

lemma ordinal_mem_iff {α : Ordinal.{u}} : α.toZFSet ∈ U ↔ α < height U := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, hU.height_toZFSet]
  simp only [ordinalPart, ZFSet.mem_sep, ZFSet.isOrdinal_toZFSet, and_true]

lemma omega_lt_height : Ordinal.omega0 < height U := hU.ordinal_mem_iff.mp hU.omega_mem

lemma height_isSuccLimit : IsSuccLimit (height U) := by
  rw [Ordinal.isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  refine ⟨ne_of_gt ((Ordinal.omega0_pos).trans hU.omega_lt_height), ?_⟩
  intro α hα
  exact hU.ordinal_mem_iff.mp (hU.ordinal_succ_mem (hU.ordinal_mem_iff.mpr hα))

theorem eq_vonNeumann_height : U = ZFSet.vonNeumann (height U) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact ZFSet.mem_vonNeumann.mpr (hU.ordinal_mem_iff.mp (hU.rank_mem hx))
  · intro hx
    have hr := hU.ordinal_mem_iff.mpr (ZFSet.mem_vonNeumann.mp hx)
    have hs := hU.vonNeumann_mem (hU.ordinal_succ_mem hr)
    exact hU.transitive.mem_trans (ZFSet.mem_vonNeumann_succ x) hs

/-- An index set in the universe cannot enumerate all ordinals below its height. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    We next show that $|x|<|\kappa|$ for every $x\in U$. Otherwise, choice gives a surjection
    $f:x\to\kappa$. All values of this map belong to $U$, so indexed-union closure gives
    $$\bigcup_{i\in x}f(i)=\bigcup\kappa=\kappa\in U,$$
    contrary to the definition of $\kappa$. In particular, $\kappa$ is an initial ordinal: its initial ordinal
    $\mu=|\kappa|$ satisfies $\mu\le\kappa$, and if $\mu<\kappa$, then $\mu\in U$ while $|\mu|=|\kappa|$,
    contradicting the bound. Thus $\kappa$ is a cardinal and $|x|<\kappa$ for every $x\in U$.
-/
theorem card_lt_height_card {x : ZFSet.{u}} (hx : x ∈ U) : x.card < (height U).card := by
  classical
  by_contra! hle
  have hcard : Cardinal.mk ((height U).toZFSet) ≤ Cardinal.mk x := by
    simpa only [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet, Cardinal.lift_le] using
      (Cardinal.lift_le.{u + 1}.mpr hle)
  change Nonempty ((height U).toZFSet ↪ x) at hcard
  obtain ⟨e⟩ := hcard
  have hpos : 0 < height U := Ordinal.omega0_pos.trans hU.omega_lt_height
  let : Nonempty ((height U).toZFSet) := ⟨⟨(0 : Ordinal.{u}).toZFSet,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr hpos⟩⟩
  let f : x → (height U).toZFSet := Function.invFun e
  have hf : Function.Surjective f := Function.invFun_surjective e.injective
  have hsub : (height U).toZFSet ⊆ U := by
    rw [hU.height_toZFSet]
    exact ZFSet.sep_subset
  have hmem (i : x) : (f i).val ∈ U := hsub (f i).property
  have hUnion := hU.indexedUnion_mem hx (fun i => (f i).val) hmem
  have heq : ZFSet.iUnion (fun i => (f i).val) = (height U).toZFSet := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := ZFSet.mem_iUnion.mp hz
      exact (ZFSet.isOrdinal_toZFSet _).mem_trans hi (f i).property
    · intro hz
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨i, hi⟩ := hf ⟨(β + 1).toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr (hU.height_isSuccLimit.succ_lt hβ)⟩
      apply ZFSet.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [congrArg Subtype.val hi]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ β)
  rw [heq] at hUnion
  exact (lt_irrefl (height U)) (hU.ordinal_mem_iff.mp hUnion)

theorem height_card_ord : (height U).card.ord = height U := by
  apply le_antisymm (Cardinal.ord_card_le _)
  by_contra! hlt
  have hc := hU.card_lt_height_card (hU.ordinal_mem_iff.mpr hlt)
  simp only [Ordinal.card_toZFSet, Cardinal.card_ord, lt_self_iff_false] at hc

/-- Initial ordinals of sets in a universe again belong to that universe. -/
theorem cardinal_ord_mem {x : ZFSet.{u}} (hx : x ∈ U) : x.card.ord.toZFSet ∈ U := by
  apply hU.ordinal_mem_iff.mpr
  rw [← hU.height_card_ord]
  exact Cardinal.ord_lt_ord.mpr (hU.card_lt_height_card hx)

end IsGrothendieckUniverse
end PolishSpaceBook.SetTheoryModels
