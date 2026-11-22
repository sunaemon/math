module

public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.SetTheory.Ordinal.Topology
public import Mathlib.SetTheory.Ordinal.FixedPoint
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Rank bounds and closed unbounded classes for finite reflection

The witnesses need not be selected definably. Their least ranks are unique,
and a small family of parameter tuples has a common ordinal bound.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open Order
universe u

/-- Inflate the supremum of all earlier values to a monotone strict majorant. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Let $f(\beta)$ be the maximum of the finitely many bounds $F_\psi(\beta)$, or $0$ if there are none, and put
    $$F(\beta)=\max\left\{\beta+1,\ \sup_{\gamma\le\beta}\bigl(f(\gamma)+1\bigr)\right\}.$$
    Then $F$ is nondecreasing, $F(\beta)>\beta$, and $F_\psi(\beta)\le F(\beta)$ for every quantified subformula.
-/
def reflectionMajorant (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) : Ordinal.{u} :=
  max (β + 1) (⨆ γ : Set.Iic β, f γ.val + 1)

theorem reflectionMajorant_gt (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) :
    β < reflectionMajorant f β :=
  (Order.lt_succ β).trans_le (le_max_left _ _)

theorem le_reflectionMajorant (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) :
    f β ≤ reflectionMajorant f β :=
  (le_of_lt (Order.lt_succ (f β))).trans
    ((Ordinal.le_iSup (fun γ : Set.Iic β => f γ.val + 1) ⟨β, show β ≤ β from le_rfl⟩).trans (le_max_right _ _))

theorem reflectionMajorant_monotone (f : Ordinal.{u} → Ordinal.{u}) :
    Monotone (reflectionMajorant f) := by
  intro α β h
  apply max_le
  · exact (Order.succ_le_succ h).trans (le_max_left _ _)
  · apply Ordinal.iSup_le
    intro γ
    exact (Ordinal.le_iSup (fun δ : Set.Iic β => f δ.val + 1)
      ⟨γ.val, γ.property.trans h⟩).trans (le_max_right _ _)

/-- Nonzero ordinals closed under a given strict majorant. -/
def reflectionClosurePoints (f : Ordinal.{u} → Ordinal.{u}) : Set Ordinal.{u} :=
  {α | 0 < α ∧ ∀ β < α, reflectionMajorant f β < α}

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Let $C$ consist of the nonzero ordinals $\alpha$ such that $F(\beta)<\alpha$ for every $\beta<\alpha$.
    These ordinals are limits, since $\beta+1\le F(\beta)<\alpha$ whenever $\beta<\alpha$.
    To find one above any given ordinal $\gamma$, set
    $$\alpha_0=\gamma,\qquad \alpha_{n+1}=F(\alpha_n),\qquad
    \alpha=\sup_{n<\omega}\alpha_n.$$
    The sequence is strictly increasing. For $\beta<\alpha$, choose $n$ with $\beta<\alpha_n$; then
    $$F(\beta)\le F(\alpha_n)=\alpha_{n+1}<\alpha.$$
    Thus $\alpha\in C$ and $\gamma<\alpha$.
-/
theorem reflectionClosurePoints_unbounded (f : Ordinal.{u} → Ordinal.{u}) (γ : Ordinal.{u}) :
    ∃ α ∈ reflectionClosurePoints f, γ < α := by
  let g := reflectionMajorant f
  let s : ℕ → Ordinal.{u} := fun n => g^[n] γ
  have hs (n : ℕ) : s (n + 1) = g (s n) := Function.iterate_succ_apply' g n γ
  have hstep (n : ℕ) : s n < s (n + 1) := by
    rw [hs]
    exact reflectionMajorant_gt f _
  let α : Ordinal.{u} := ⨆ n, s n
  have hsα (n : ℕ) : s n < α := (hstep n).trans_le (Ordinal.le_iSup s (n + 1))
  have hγα : γ < α := hsα 0
  refine ⟨α, ⟨lt_of_le_of_lt (show 0 ≤ γ from zero_le) hγα, ?_⟩, hγα⟩
  intro β hβ
  obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hβ
  apply (reflectionMajorant_monotone f hn.le).trans_lt
  change g (s n) < α
  rw [← hs]
  exact hsα (n + 1)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    The class $C$ is closed. Indeed, if $\alpha$ is the supremum of a nonempty set of members of $C$, then
    $\alpha>0$. For each $\beta<\alpha$, some member $\delta$ of that set satisfies $\beta<\delta$, and hence
    $F(\beta)<\delta\le\alpha$. Therefore $\alpha\in C$.
-/
theorem reflectionClosurePoints_closed (f : Ordinal.{u} → Ordinal.{u}) :
    IsClosed (reflectionClosurePoints f) := by
  rw [Ordinal.isClosed_iff_iSup]
  intro ι hι s hs
  let i := Classical.choice hι
  refine ⟨(hs i).1.trans_le (Ordinal.le_iSup s i), ?_⟩
  intro β hβ
  obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp hβ
  exact ((hs j).2 β hj).trans_le (Ordinal.le_iSup s j)

theorem reflectionClosurePoints_isSuccLimit {f : Ordinal.{u} → Ordinal.{u}} {α : Ordinal.{u}}
    (hα : α ∈ reflectionClosurePoints f) : IsSuccLimit α := by
  rw [Ordinal.isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  refine ⟨ne_of_gt hα.1, fun β hβ => ?_⟩
  exact (le_max_left (β + 1) _).trans_lt (hα.2 β hβ)

/-- A nonempty class of witnesses has a witness of least rank. -/
theorem exists_least_rank_witness (P : ZFSet.{u} → Prop) (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x.rank ≤ y.rank := by
  let S : Set Ordinal.{u} := {α | ∃ x, P x ∧ x.rank = α}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x.rank, x, hx, rfl⟩
  obtain ⟨α, ⟨x, hx, he⟩, hmin⟩ := wellFounded_lt.has_min S hS
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [he]
  exact le_of_not_gt (hmin y.rank ⟨y, hy, rfl⟩)

/-- Choose one least-rank witness, using the empty set when none exists. -/
def leastRankWitness (P : ZFSet.{u} → Prop) : ZFSet.{u} := by
  classical
  exact if h : ∃ x, P x then Classical.choose (exists_least_rank_witness P h) else ∅

theorem leastRankWitness_spec (P : ZFSet.{u} → Prop) (h : ∃ x, P x) :
    P (leastRankWitness P) ∧ ∀ y, P y → (leastRankWitness P).rank ≤ y.rank := by
  simp only [leastRankWitness, dite_eq_left h]
  exact Classical.choose_spec (exists_least_rank_witness P h)

/-- The successor of the supremum of least witness ranks at a fixed stage. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use implication, falsity, and universal quantification as the logical primitives; conjunction, negation,
    and existential quantification are their usual abbreviations. Close the finite list $\Phi$ under subformulas.
    For each quantified subformula $\forall x\,\psi(x,\vec y)$ and parameter tuple $\vec a$, let
    $r_\psi(\vec a)$ be the least rank of a counterexample to $\psi(x,\vec a)$ if one exists, and let it be $0$
    otherwise. This is the witness-rank construction for the existential formula $\exists x\,\neg\psi(x,\vec a)$.
    For each ordinal $\beta$, set
    $$F_\psi(\beta)=\sup\{r_\psi(\vec a):\vec a\in V_\beta\}+1.$$
    Here the tuples have the fixed finite length appropriate to the subformula, and the supremum of the empty
    set of ordinals is $0$. Replacement bounds the set of least witness ranks; choosing witnesses uniformly is
    unnecessary.
-/
def reflectionWitnessBound {n : ℕ} (P : (Fin n → ZFSet.{u}) → ZFSet.{u} → Prop)
    (β : Ordinal.{u}) : Ordinal.{u} :=
  (⨆ xs : Fin n → ZFSet.vonNeumann β, (leastRankWitness (P (fun i => (xs i).val))).rank) + 1

theorem reflectionWitnessBound_spec {n : ℕ}
    (P : (Fin n → ZFSet.{u}) → ZFSet.{u} → Prop) (β : Ordinal.{u})
    (xs : Fin n → ZFSet.vonNeumann β) (h : ∃ x, P (fun i => (xs i).val) x) :
    ∃ x, P (fun i => (xs i).val) x ∧ x.rank < reflectionWitnessBound P β := by
  refine ⟨leastRankWitness (P (fun i => (xs i).val)), (leastRankWitness_spec _ h).1, ?_⟩
  exact (Ordinal.le_iSup (fun ys : Fin n → ZFSet.vonNeumann β =>
    (leastRankWitness (P (fun i => (ys i).val))).rank) xs).trans_lt (Order.lt_succ _)

end PolishSpaceBook.SetTheoryModels
