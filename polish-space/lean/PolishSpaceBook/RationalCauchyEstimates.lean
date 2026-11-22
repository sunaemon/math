module

public import PolishSpaceBook.RationalMetricEstimates

@[expose] public section

/-! # Rational witnesses that a sequence is not a fast Cauchy name

These estimates require neither completeness nor density and make no
computational assumptions. Closed lambda programs implement the tests later.
-/
namespace PolishSpaceBook
open Set
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X}
namespace RationalMetricApproximation
variable (A : RationalMetricApproximation q)

def invalidNameTest (p : ℕ → ℕ) (z : ℕ × (ℕ × ℕ)) : Bool :=
  decide (z.1 ≤ z.2.1) && decide
    (((RationalCode.dyadic z.1).add (RationalCode.dyadic z.2.2)).lt
      (A.approx (p z.1, (p z.2.1, z.2.2))))

theorem invalidNameTest_iff (p : ℕ → ℕ) (n m k : ℕ) :
    A.invalidNameTest p (n, (m, k)) = true ↔ n ≤ m ∧
      (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ k <
        (RationalCode.value (A.approx (p n, (p m, k))) : ℝ) := by
  simp only [invalidNameTest, Bool.and_eq_true, decide_eq_true_eq, RationalCode.lt_iff]
  rw [← Rat.cast_lt (K := ℝ)]
  simp

theorem not_cauchyName_of_test (p : ℕ → ℕ) (n m k : ℕ)
    (h : A.invalidNameTest p (n, (m, k)) = true) : ¬ IsCauchyName q p := by
  obtain ⟨hnm, ht⟩ := (A.invalidNameTest_iff p n m k).mp h
  intro hp
  have hbound := hp n m hnm
  have ha := (abs_le.mp (A.error (p n) (p m) k)).2
  linarith

theorem exists_invalidNameTest (p : ℕ → ℕ) (h : ¬ IsCauchyName q p) :
    ∃ n m k, A.invalidNameTest p (n, (m, k)) = true := by
  classical
  simp only [IsCauchyName, not_forall] at h
  obtain ⟨n, m, hnm, hd⟩ := h
  have hd : (1 / 2 : ℝ) ^ n < dist (q (p n)) (q (p m)) := lt_of_not_ge hd
  have hgap : 0 < (dist (q (p n)) (q (p m)) - (1 / 2 : ℝ) ^ n) / 2 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, m, k, (A.invalidNameTest_iff p n m k).mpr ⟨hnm, ?_⟩⟩
  have ha := (abs_le.mp (A.error (p n) (p m) k)).1
  linarith

/-- One numerical stage enumerates all triples via the fixed bijective pairing. -/
def invalidNameStage (p : ℕ → ℕ) (j : ℕ) : Bool :=
  A.invalidNameTest p (j.unpair.1, j.unpair.2.unpair)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Enumerate all triples $(n,m,k)$ by the stage index $j=\NatPair{n}{\NatPair{m}{k}}$. For each triple, read $p(n)$ and
    $p(m)$ and test
    $$
    n\le m
    \quad\text{and}\quad
    2^{-n}+2^{-k}<A(p(n),p(m),k).
    $$
    Every test terminates. Success implies $d(q_{p(n)},q_{p(m)})>2^{-n}$ by the approximation error bound, so it certifies
    an invalid name. Conversely, an invalid name has some $n\le m$ with this strict inequality. Choose $k$ so that
    $2\cdot2^{-k}$ is smaller than the positive gap $d(q_{p(n)},q_{p(m)})-2^{-n}$. The approximation error bound then makes
    the displayed test succeed.
-/
theorem exists_invalidNameStage_iff (p : ℕ → ℕ) :
    (∃ j, A.invalidNameStage p j = true) ↔ ¬ IsCauchyName q p := by
  constructor
  · rintro ⟨j,hj⟩
    exact A.not_cauchyName_of_test p _ _ _ hj
  · intro h
    obtain ⟨n,m,k,hk⟩ := A.exists_invalidNameTest p h
    exact ⟨Nat.pair n (Nat.pair m k),by simpa [invalidNameStage] using hk⟩

theorem invalidNameStage_eq_of_agree (p r : ℕ → ℕ) (j : ℕ)
    (hn : p j.unpair.1 = r j.unpair.1) (hm : p j.unpair.2.unpair.1 = r j.unpair.2.unpair.1) :
    A.invalidNameStage p j = A.invalidNameStage r j := by
  simp only [invalidNameStage,invalidNameTest,hn,hm]

end RationalMetricApproximation
end PolishSpaceBook
