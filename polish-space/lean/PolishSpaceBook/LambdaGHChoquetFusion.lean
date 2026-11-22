module

public import PolishSpaceBook.LambdaGHChoquetStates

@[expose] public section

/-! # Fusion of the pointed states in a strong Choquet play

The point coordinates and each previously introduced witness coordinate
stabilize. Closedness is applied to actual pairs in the original tree body,
not to the closure of a projected set.
-/
namespace PolishSpaceBook
open Set Filter Topology
namespace LambdaTree.GHChoquet

theorem stable_after {α : Type*} (f : ℕ → α) (n : ℕ)
    (hs : ∀ m, n ≤ m → f (m+1) = f m) (m : ℕ) (hnm : n ≤ m) : f m = f n := by
  induction m,hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (hs m hnm).trans ih

/-- Every trace in a coherent pointed play contains the common limit. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    In a play following this strategy, the compatible prefixes $u_n$ determine a point $x$, and for
    each fixed $i$ the prefixes $v_{i,n}$ for $n\ge i$ determine a witness $y_i$. To justify membership
    in the tree body, consider the actual pairs $(x_n,y_{i,n})\in\TreeBody{T_i}$ for $n\ge i$. Their fixed initial
    segments grow without bound, so these pairs converge to $(x,y_i)$ in the ordinary product topology.
    The body $\TreeBody{T_i}$ is closed in that topology, hence $(x,y_i)\in\TreeBody{T_i}$. Moreover, $x$ extends every
    $u_n$, and $y_i$ extends $v_{i,n}$ whenever $i\le n$. Thus $x\in V_n\IncludedIn U_n$ for every $n$,
    and Player II wins.
-/
theorem states_fusion {ε : ℕ → ℕ} (q : ℕ → State ε)
    (hl : ∀ n, (q n).level = n)
    (hp : ∀ n k, k < n → (q (n+1)).point k = (q n).point k)
    (ht : ∀ n i, i < n → (q (n+1)).tree i = (q n).tree i)
    (hw : ∀ n i k, i < n → k < n → (q (n+1)).witness i k = (q n).witness i k)
    (hq : ∀ n, (q n).point ∈ (q n).trace) :
    ∃ x, ∀ n, x ∈ (q n).trace := by
  classical
  have point_stable (n m : ℕ) (hnm : n ≤ m) (k : ℕ) (hk : k < n) :
      (q m).point k = (q n).point k :=
    stable_after (fun j => (q j).point k) n (fun j hj => hp j k (hk.trans_le hj)) m hnm
  have tree_stable (n m : ℕ) (hnm : n ≤ m) (i : ℕ) (hi : i < n) :
      (q m).tree i = (q n).tree i :=
    stable_after (fun j => (q j).tree i) n (fun j hj => ht j i (hi.trans_le hj)) m hnm
  have witness_stable (n m : ℕ) (hnm : n ≤ m) (i k : ℕ) (hi : i < n) (hk : k < n) :
      (q m).witness i k = (q n).witness i k :=
    stable_after (fun j => (q j).witness i k) n
      (fun j hj => hw j i k (hi.trans_le hj) (hk.trans_le hj)) m hnm
  let x : FusionReal := fun k => (q (k+1)).point k
  let y : ℕ → FusionReal := fun i k => (q (max (i+1) (k+1))).witness i k
  have hx (n k : ℕ) (hk : k < n) : x k = (q n).point k :=
    (point_stable (k+1) n (by omega) k (by omega)).symm
  have hy (i n k : ℕ) (hi : i < n) (hk : k < n) : y i k = (q n).witness i k :=
    (witness_stable (max (i+1) (k+1)) n (by omega) i k (by omega) (by omega)).symm
  have hbody (i : ℕ) : (x,y i) ∈ pairTreeBody ((q (i+1)).tree i).tree := by
    have hex (n : ℕ) : ∃ v, v ∈ fusionCylinder
        (finitePrefix ((q (i+1+n)).witness i) (q (i+1+n)).level) ∧
        ((q (i+1+n)).point,v) ∈ pairTreeBody ((q (i+1+n)).tree i).tree :=
      ((hq (i+1+n)).2 i (by rw [hl]; omega)).2
    choose v hv hvbody using hex
    have hpoint : Tendsto (fun n => (q (i+1+n)).point) atTop (𝓝 x) := by
      apply tendsto_pi_nhds.mpr
      intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (k+1)] with n hn
      exact hx (i+1+n) k (by omega)
    have hwitness : Tendsto v atTop (𝓝 (y i)) := by
      apply tendsto_pi_nhds.mpr
      intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (k+1)] with n hn
      have hk : k < (q (i+1+n)).level := by rw [hl]; omega
      exact (hy i (i+1+n) k (by omega) (by omega)).trans ((hv n) ⟨k,hk⟩).symm
    apply (isClosed_pairTreeBody _).mem_of_tendsto (hpoint.prodMk_nhds hwitness)
    apply Eventually.of_forall
    intro n
    have htree := tree_stable (i+1) (i+1+n) (by omega) i (by omega)
    simpa only [htree] using hvbody n
  refine ⟨x,fun n => ?_⟩
  have hxprefix : x ∈ fusionCylinder (finitePrefix (q n).point (q n).level) := by
    intro k
    exact hx n k.val (by simpa only [hl] using k.isLt)
  refine ⟨hxprefix,fun i hi => ⟨hxprefix,y i,?_,?_⟩⟩
  · intro k
    exact hy i n k.val (by simpa only [hl] using hi) (by simpa only [hl] using k.isLt)
  · have hi' : i < n := by simpa only [hl] using hi
    have htree := tree_stable (i+1) n (by omega) i (by omega)
    simpa only [htree] using hbody i

end LambdaTree.GHChoquet
end PolishSpaceBook
