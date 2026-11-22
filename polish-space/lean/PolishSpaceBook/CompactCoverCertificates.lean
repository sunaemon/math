module

public import PolishSpaceBook.LambdaMetricBalls
public import PolishSpaceBook.LambdaListAccess

@[expose] public section

/-! # Finite-net certificates for covers by rational metric balls -/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
universe u
variable {X : Type u} [MetricSpace X]

def IsDyadicNetSequence (q : ℕ → X) (E : ℕ → List ℕ) : Prop :=
  ∀ n x, ∃ i < (E n).length, dist x (q ((E n).getD i 0)) < (1/2:ℝ)^n

def coverBallCenter (b j : ℕ) : ℕ := ((NatListCode.decode b).getD j 0).unpair.1
def coverBallRadius (b j : ℕ) : RationalCode :=
  RationalCode.ofNat (((NatListCode.decode b).getD j 0).unpair.2)

def rationalBallListCovers (q : ℕ → X) (b : ℕ) : Prop :=
  ∀ x, ∃ j < (NatListCode.decode b).length,
    dist x (q (coverBallCenter b j)) < (coverBallRadius b j).value

def netCoverCertificate {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (b n : ℕ) : Prop :=
  ∀ i < (E n).length, ∃ j < (NatListCode.decode b).length,
    (A.approx ((E n).getD i 0,(coverBallCenter b j,n))).value + 2*(1/2:ℚ)^n <
      (coverBallRadius b j).value

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Put $\varepsilon_n:=2^{-n}$ and let $A(u,v,n)$ be the rational distance approximation, with
    $$|A(u,v,n)-d(q_u,q_v)|\le\varepsilon_n.$$
    At stage $n$, compute $E_n$ and test the finite condition
    $$\forall k<\ell_n\;\exists j<m:\quad A(e_{n,k},i_j,n)+2\varepsilon_n<r_j.$$
    Every comparison is rational and terminates. If the test succeeds, choose for each $x\in K$ a net point with
    $d(x,q_{e_{n,k}})<\varepsilon_n$ and a successful ball for that point. Then
    $$d(x,q_{i_j})\le d(x,q_{e_{n,k}})+d(q_{e_{n,k}},q_{i_j})
    < A(e_{n,k},i_j,n)+2\varepsilon_n<r_j.$$
    Thus every successful stage certifies the proposed cover.
-/
theorem netCoverCertificate_sound {q : ℕ → X} (A : RationalMetricApproximation q)
    {E : ℕ → List ℕ} (hE : IsDyadicNetSequence q E) {b n : ℕ}
    (h : netCoverCertificate A E b n) : rationalBallListCovers q b := by
  intro x
  obtain ⟨i,hi,hxi⟩ := hE n x
  obtain ⟨j,hj,ht⟩ := h i hi
  refine ⟨j,hj,?_⟩
  have ha := (abs_le.mp (A.error ((E n).getD i 0) (coverBallCenter b j) n)).1
  have htri := dist_triangle x (q ((E n).getD i 0)) (q (coverBallCenter b j))
  have ht' : ((A.approx ((E n).getD i 0,(coverBallCenter b j,n))).value:ℝ) +
      2*(1/2:ℝ)^n < (coverBallRadius b j).value := by
    rw [← Rat.cast_lt (K := ℝ)] at ht
    push_cast at ht
    exact ht
  linarith

/-- Compactness makes a positive rational margin uniform over the whole space. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $\varepsilon_n:=2^{-n}$ and consider the increasing open sets
    $$U_n:=\bigcup_{j<m}\Ball{c_j}{r_j-4\varepsilon_n}.$$
    For every $x\in K$, some $r_j-d(x,c_j)$ is positive, so $x\in U_n$ for all sufficiently large $n$.
    Hence the sets $U_n$ cover $K$. Compactness gives a finite subcover; since they are increasing, one $U_N$
    already covers $K$. This is the required uniform margin, including when $K$ is empty.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform ball-cover margin}{Uniform ball-cover margin}]
    Let $K$ be a compact metric space and let $((c_j,r_j))_{j<m}$ be a finite list of balls covering $K$.
    There is some $N\in\NN$ such that every $x\in K$ satisfies
    $$d(x,c_j)+4\cdot 2^{-N}<r_j$$
    for some $j<m$.
    \end{lemma*}
-/
theorem finiteBallCover_uniform_margin [CompactSpace X] {m : ℕ}
    (c : Fin m → X) (r : Fin m → ℝ)
    (hcover : ∀ x, ∃ j, dist x (c j) < r j) :
    ∃ n, ∀ x, ∃ j, dist x (c j) + 4*(1/2:ℝ)^n < r j := by
  let U : ℕ → Set X := fun n => ⋃ j : Fin m,
    Metric.ball (c j) (r j-4*(1/2:ℝ)^n)
  have ho (n : ℕ) : IsOpen (U n) := isOpen_iUnion (fun _ => Metric.isOpen_ball)
  have hcover : (univ : Set X) ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨j,hx⟩ := hcover x
    have hgap : 0 < (r j-dist x (c j))/4 := by linarith
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1/2:ℝ)<1)
    apply mem_iUnion.mpr
    refine ⟨n,mem_iUnion.mpr ⟨j,?_⟩⟩
    change dist x (c j) < r j-4*(1/2:ℝ)^n
    linarith
  have hmono : Monotone U := by
    intro n m hnm x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    rw [Metric.mem_ball] at hj ⊢
    have he : (1/2:ℝ)^m ≤ (1/2:ℝ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
    linarith
  obtain ⟨n,hn⟩ := isCompact_univ.elim_directed_cover U ho hcover hmono.directed_le
  refine ⟨n,fun x => ?_⟩
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hn (mem_univ x))
  refine ⟨j,?_⟩
  rw [Metric.mem_ball] at hj
  linarith

/-- The rational-code instance used by the closed cover-search program. -/
theorem rationalBallListCovers_uniform_margin [CompactSpace X] (q : ℕ → X) {b : ℕ}
    (hb : rationalBallListCovers q b) : ∃ n, ∀ x, ∃ j < (NatListCode.decode b).length,
      dist x (q (coverBallCenter b j)) + 4*(1/2:ℝ)^n < (coverBallRadius b j).value := by
  obtain ⟨n, hn⟩ := finiteBallCover_uniform_margin
    (fun j : Fin (NatListCode.decode b).length => q (coverBallCenter b j.val))
    (fun j => (coverBallRadius b j.val).value) (fun x => by
      obtain ⟨j, hj, hx⟩ := hb x
      exact ⟨⟨j, hj⟩, hx⟩)
  exact ⟨n, fun x => by obtain ⟨j, hj⟩ := hn x; exact ⟨j.val, j.isLt, hj⟩⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Conversely, suppose that $B$ covers $K$. The \termuse{uniform ball-cover margin} gives a stage $N$
    at which every net point belongs to a ball with
    $$d(q_{e_{N,k}},q_{i_j})+4\varepsilon_N<r_j.$$
    The upper error estimate then gives
    $$A(e_{N,k},i_j,N)+2\varepsilon_N
    \le d(q_{e_{N,k}},q_{i_j})+3\varepsilon_N<r_j.$$
    Thus the finite test succeeds at stage $N$.
-/
theorem netCoverCertificate_complete [CompactSpace X] {q : ℕ → X}
    (A : RationalMetricApproximation q) (E : ℕ → List ℕ) {b : ℕ}
    (hb : rationalBallListCovers q b) : ∃ n, netCoverCertificate A E b n := by
  obtain ⟨n,hn⟩ := rationalBallListCovers_uniform_margin q hb
  refine ⟨n,fun i _ => ?_⟩
  obtain ⟨j,hj,hm⟩ := hn (q ((E n).getD i 0))
  refine ⟨j,hj,?_⟩
  have ha := (abs_le.mp (A.error ((E n).getD i 0) (coverBallCenter b j) n)).2
  have he : 0 < (1/2:ℝ)^n := by positivity
  have hreal : ((A.approx ((E n).getD i 0,(coverBallCenter b j,n))).value:ℝ) +
      2*(1/2:ℝ)^n < (coverBallRadius b j).value := by linarith
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  exact hreal

theorem rationalBallListCovers_iff_certificate [CompactSpace X] {q : ℕ → X}
    (A : RationalMetricApproximation q) {E : ℕ → List ℕ} (hE : IsDyadicNetSequence q E) (b : ℕ) :
    rationalBallListCovers q b ↔ ∃ n, netCoverCertificate A E b n :=
  ⟨netCoverCertificate_complete A E,fun ⟨_,hn⟩ => netCoverCertificate_sound A hE hn⟩

end PolishSpaceBook
