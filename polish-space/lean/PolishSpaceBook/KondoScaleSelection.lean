module

public import PolishSpaceBook.KondoMinimum
public import PolishSpaceBook.AnalyticSetsSuslinSchemes

@[expose] public section

/-! # The alternating scale-rank and coordinate construction

Scale existence is a cited input. The construction and uniqueness of the
successive-minimum point are proved here, without assuming a selector.
-/
namespace PolishSpaceBook.Kondo
noncomputable section
open Set Filter Topology

variable {X : Type}

/-- The closure part of the cited scale machinery, on a closed Baire domain. -/
structure Scale (A : Set (X × baire_space)) (F : Set baire_space) where
  rank : ℕ → X × baire_space → Ordinal
  closed_limit : ∀ (x : X) (q : ℕ → baire_space) (y : baire_space) (a : ℕ → Ordinal),
    (∀ k, (x, q k) ∈ A) → y ∈ F → Tendsto q atTop (𝓝 y) →
    (∀ n, ∀ᶠ k in atTop, rank n (x, q k) = a n) →
    (x, y) ∈ A ∧ ∀ n, rank n (x, y) ≤ a n

variable {A : Set (X × baire_space)} {F : Set baire_space} (s : Scale A F)

def key (x : X) (n : ℕ) (y : baire_space) : Ordinal :=
  if n % 2 = 0 then s.rank (n / 2) (x, y) else (y (n / 2) : Ordinal)

@[simp] theorem key_even (x : X) (n : ℕ) (y : baire_space) :
    key s x (2 * n) y = s.rank n (x, y) := by simp [key]

@[simp] theorem key_odd (x : X) (n : ℕ) (y : baire_space) :
    key s x (2 * n + 1) y = (y n : Ordinal) := by simp [key, Nat.add_div]

/-- Every stage is minimal among candidates sharing all preceding keys. -/
def Good (x : X) (y : baire_space) : Prop :=
  (x, y) ∈ A ∧ ∀ n z, (x, z) ∈ A →
    (∀ i < n, key s x i z = key s x i y) → key s x n y ≤ key s x n z

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Use the cited scale-existence theorem to put a $\bPi^1_1$ scale $\Sequence{\varphi_n}{n\in\omega}$ on $A$.
    For fixed $x\in\pi_X(A)$, interleave the ordinal ranks and the natural coordinates as keys
    $$h_{2n}(x,y):=\varphi_n(x,y),\qquad h_{2n+1}(x,y):=y(n).$$
    View natural numbers as finite ordinals. Starting with $S_0=A_x$, let $a_i$ be the least value of $h_i(x,\cdot)$ on
    $S_i$, and put $S_{i+1}:=\{y\in S_i:h_i(x,y)=a_i\}$. Every $S_i$ is nonempty, since a nonempty set of ordinals has a
    least member. Choose $q_k\in S_{2k+2}$ for each $k$. Then $q_k(n)$ is constant for $k\ge n$, and
    $\varphi_n(x,q_k)=a_{2n}$ for $k\ge n$. The points $q_k$ converge coordinatewise to a point $y\in F$.
    The scale closure property gives $(x,y)\in A$ and $\varphi_n(x,y)\le a_{2n}$ for every $n$.
    Induction on $i$ now proves $h_i(x,y)=a_i$: the coordinate equalities follow from convergence, while at a rank step
    the preceding equalities put $y$ in $S_i$, so minimality gives the reverse inequality. Thus $y$ realizes every
    successive minimum. Two points realizing every successive minimum have equal keys by induction and hence equal
    coordinates, so this point is unique.
-/
theorem exists_good (hF : IsClosed F) (hAF : ∀ p ∈ A, p.2 ∈ F)
    (x : X) (hne : ∃ y, (x, y) ∈ A) : ∃ y, Good s x y := by
  classical
  let S : {S : Set baire_space // S.Nonempty} := ⟨{y | (x, y) ∈ A}, hne⟩
  let m := minimum (key s x) S
  let q : ℕ → baire_space := fun k => sample (key s x) S (2 * k + 1)
  let y : baire_space := fun n => q n n
  have hq (k : ℕ) : (x, q k) ∈ A ∧
      ∀ i ≤ 2 * k + 1, key s x i (q k) = m i :=
    sample_spec (key s x) S (2 * k + 1)
  have hcoord (n : ℕ) : (y n : Ordinal) = m (2 * n + 1) := by
    simpa [y] using (hq n).2 (2 * n + 1) le_rfl
  have hstable (n k : ℕ) (hnk : n ≤ k) : q k n = y n := by
    have he := (hq k).2 (2 * n + 1) (by omega)
    simp only [key_odd] at he
    exact_mod_cast he.trans (hcoord n).symm
  have hlim : Tendsto q atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    exact (hstable n k hk).symm
  have hyF : y ∈ F := hF.mem_of_tendsto hlim
    (Eventually.of_forall fun k => hAF _ (hq k).1)
  have hrank : ∀ n, ∀ᶠ k in atTop, s.rank n (x, q k) = m (2 * n) := by
    intro n
    filter_upwards [eventually_ge_atTop n] with k hk
    simpa using (hq k).2 (2 * n) (by omega)
  obtain ⟨hyA, hybound⟩ := s.closed_limit x q y (fun n => m (2 * n))
    (fun k => (hq k).1) hyF hlim hrank
  have hkeys : ∀ i, key s x i y = m i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · have he : i = 2 * (i / 2) := by omega
        have hl := minimum_le_of_history (key s x) S i hyA (fun j hj => ih j hj)
        have hu : key s x i y ≤ m i := by
          rw [he, key_even]
          exact hybound _
        exact le_antisymm hu hl
      · have he : i = 2 * (i / 2) + 1 := by omega
        rw [he, key_odd]
        exact hcoord _
  refine ⟨y, hyA, fun n z hz hh => ?_⟩
  rw [hkeys n]
  exact minimum_le_of_history (key s x) S n hz (fun i hi => (hh i hi).trans (hkeys i))

theorem good_unique {x : X} {y z : baire_space} (hy : Good s x y) (hz : Good s x z) :
    y = z := by
  have hk : ∀ i, key s x i y = key s x i z := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      exact le_antisymm (hy.2 i z hz.1 (fun j hj => (ih j hj).symm))
        (hz.2 i y hy.1 (fun j hj => ih j hj))
  funext n
  have hn := hk (2 * n + 1)
  simp only [key_odd] at hn
  exact_mod_cast hn

end
end PolishSpaceBook.Kondo
