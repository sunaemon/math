module

public import PolishSpaceBook.LambdaGHTopology
public import PolishSpaceBook.StrongChoquetGame

@[expose] public section

/-! # Pointed witness-prefix states for the Gandy--Harrington game

A state remembers finitely many pair trees and prefixes of witnesses for
each tree. The unused tails of the stored sequences do not affect its open
trace. Each legal input extends every old prefix while adding one new tree.
-/
namespace PolishSpaceBook
open Set Topology
namespace LambdaTree
namespace GHChoquet

def finitePrefix (x : FusionReal) (n : ℕ) : FusionPrefix n := fun i => x i.val

structure State (ε : ℕ → ℕ) where
  level : ℕ
  point : FusionReal
  tree : ℕ → PairTree ε
  witness : ℕ → FusionReal

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Respond with
    $$\begin{aligned}
     V_n:=\{z\in\BaireSpace:\ &u_n\preceq z,\quad
      \forall i\le n\ \exists y\in\BaireSpace\\
     &v_{i,n}\preceq y\ \land\ (z,y)\in\TreeBody{T_i}\}.
    \end{aligned}$$
    Finite-prefix restrictions and finite intersections preserve pair-tree presentations at
    $\varepsilon$, so $V_n$ is $\lSigma^1_1(\varepsilon)$ and hence open. The chosen witnesses show that
    $x_n\in V_n$. The condition for $i=n$ gives $V_n\IncludedIn B_n\IncludedIn U_n$, and preservation of
    old prefixes gives $V_n\IncludedIn V_{n-1}$ when $n>0$. This is a legal response. Fix all choices as
    functions of the finite history. This defines a strategy; it does not assert a computable procedure
    for choosing witnesses from arbitrary points.
-/
def State.trace {ε : ℕ → ℕ} (q : State ε) : Set FusionReal :=
  {x | x ∈ fusionCylinder (finitePrefix q.point q.level) ∧ ∀ i < q.level,
    x ∈ witnessProjection (pairTreeBody (q.tree i).tree)
      (finitePrefix q.point q.level) (finitePrefix (q.witness i) q.level)}

theorem projected_bounded_inter {ε : ℕ → ℕ} (A : ℕ → Set FusionReal)
    (hA : ∀ i, Projected ε (A i)) (n : ℕ) : Projected ε {x | ∀ i < n, x ∈ A i} := by
  induction n with
  | zero => simpa using projected_cyl ε []
  | succ n ih =>
    have he : {x | ∀ i < n+1, x ∈ A i} = {x | ∀ i < n, x ∈ A i} ∩ A n := by
      ext x
      constructor
      · intro h; exact ⟨fun i hi => h i (by omega),h n (by omega)⟩
      · rintro ⟨h,hlast⟩ i hi
        by_cases he : i = n
        · simpa [he] using hlast
        · exact h i (by omega)
    rw [he]
    exact ih.inter (hA n)

theorem State.projected {ε : ℕ → ℕ} (q : State ε) : Projected ε q.trace :=
  (projected_fusionCylinder ε (finitePrefix q.point q.level)).inter
    (projected_bounded_inter _ (fun i => projected_witnessProjection (q.tree i) _ _) q.level)

theorem State.isOpen {ε : ℕ → ℕ} (q : State ε) :
    @IsOpen _ (parameterGHTopology ε) q.trace := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  exact (parameterGHBasis_isBasis ε).isOpen q.projected

def initial (ε : ℕ → ℕ) : State ε :=
  ⟨0,fun _ => 0,fun _ => indexedTree ε 0,fun _ _ => 0⟩

@[simp] theorem initial_trace (ε : ℕ → ℕ) : (initial ε).trace = univ := by
  ext x
  simp [State.trace,initial,finitePrefix,fusionCylinder]

/-- One response extends all old prefixes and adds a presentation of the
current basic neighborhood. Choice is used only to select witnesses. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Player II remembers the trees already chosen and finite prefixes of the point and of one witness
    for each tree. For every $i<n$, membership of $x_n$ in $V_{n-1}$ supplies a witness $y_{i,n}$ through
    $T_i$ extending the previously fixed witness prefix. Choose also a witness $y_{n,n}$ through $T_n$ at
    $x_n$. Put
    $$u_n:=\restrict{x_n}{n+1},\qquad v_{i,n}:=\restrict{y_{i,n}}{n+1}\quad(i\le n).$$
    For $n>0$, the point prefix $u_n$ extends $u_{n-1}$, and $v_{i,n}$ extends $v_{i,n-1}$ for each $i<n$.
    Thus every old prefix is preserved and gains one coordinate.
-/
theorem extend {ε : ℕ → ℕ} (q : State ε) (x : FusionReal) (hx : x ∈ q.trace)
    (U : Set FusionReal) (hU : @IsOpen _ (parameterGHTopology ε) U) (hxU : x ∈ U) :
    ∃ r : State ε,
      r.level = q.level+1 ∧ r.point = x ∧ x ∈ r.trace ∧ r.trace ⊆ U ∧
      r.trace ⊆ q.trace ∧
      (∀ k < q.level, r.point k = q.point k) ∧
      (∀ i < q.level, r.tree i = q.tree i ∧ ∀ k < q.level, r.witness i k = q.witness i k) := by
  classical
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  obtain ⟨B,hB,hxB,hBU⟩ := (parameterGHBasis_isBasis ε).exists_subset_of_mem_open hxU hU
  obtain ⟨T,hT⟩ := hB
  obtain ⟨y,hy⟩ : ∃ y, (x,y) ∈ pairTreeBody T.tree := by
    rw [hT] at hxB
    exact hxB
  have hold : ∀ i, i < q.level → ∃ z, z ∈ fusionCylinder (finitePrefix (q.witness i) q.level) ∧
      (x,z) ∈ pairTreeBody (q.tree i).tree := fun i hi => (hx.2 i hi).2
  let w : ℕ → FusionReal := fun i => if hi : i < q.level then (hold i hi).choose else y
  let r : State ε := ⟨q.level+1,x,(fun i => if i < q.level then q.tree i else T),w⟩
  have hw (i : ℕ) (hi : i < q.level) :
      w i ∈ fusionCylinder (finitePrefix (q.witness i) q.level) ∧ (x,w i) ∈ pairTreeBody (q.tree i).tree := by
    simpa only [w,dite_eq_left hi] using (hold i hi).choose_spec
  have hwbody (i : ℕ) : (x,w i) ∈ pairTreeBody (r.tree i).tree := by
    by_cases hi : i < q.level
    · simpa only [r,ite_eq_left hi] using (hw i hi).2
    · simpa only [r,w,ite_eq_right hi,dite_eq_right hi] using hy
  have hx' : x ∈ r.trace := by
    refine ⟨fun _ => rfl,fun i hi => ⟨fun _ => rfl,w i,(fun _ => rfl),hwbody i⟩⟩
  have hsub : r.trace ⊆ U := by
    intro z hz
    have hlast := (hz.2 q.level (by simp [r])).2
    apply hBU
    rw [hT]
    obtain ⟨v,_,hv⟩ := hlast
    exact ⟨v,by simpa [r] using hv⟩
  have hprev : r.trace ⊆ q.trace := by
    intro z hz
    have hpoint : z ∈ fusionCylinder (finitePrefix q.point q.level) := by
      intro k
      exact (hz.1 ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩).trans (hx.1 k)
    refine ⟨hpoint,fun i hi => ⟨hpoint,?_⟩⟩
    obtain ⟨v,hv,hbody⟩ := (hz.2 i (by simpa [r] using Nat.lt_succ_of_lt hi)).2
    refine ⟨v,?_,by simpa only [r,ite_eq_left hi] using hbody⟩
    intro k
    exact (hv ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩).trans ((hw i hi).1 k)
  refine ⟨r,rfl,rfl,hx',hsub,hprev,fun k hk => hx.1 ⟨k,hk⟩,?_⟩
  intro i hi
  exact ⟨by simp [r,hi],fun k hk => (hw i hi).1 ⟨k,hk⟩⟩

end GHChoquet
end LambdaTree
end PolishSpaceBook
