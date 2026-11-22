module

public import PolishSpaceBook.NonnegativeRealCutReflection

@[expose] public section

/-! # Addition of nonnegative real codes, including the empty cut for zero -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels
universe u

/-- Zero is an admissible lower approximation even when the strict cut is empty. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $a,b\in\omega$, put
    $$\RealCutApprox{C}{a}{b}\longleftrightarrow
    0<b\ \land\ (a=0\ \lor\ \langle a,b\rangle\in C).$$
    If $C=\NonnegativeRealCut{r}$ with $r\ge0$, every such fraction satisfies $a/b\le r$.
    For every $\varepsilon>0$ one can choose such a fraction with $r-\varepsilon<a/b$:
    use $0/1$ when $r<\varepsilon$, and otherwise choose a rational strictly between $r-\varepsilon$ and $r$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finite additivity requires the sum of two coded nonnegative reals. Since the code of zero is empty,
    we must allow zero as a lower approximation even when it does not belong to the strict cut.
-/
def cutLowerApproximation (C : ZFSet.{u}) (a b : ℕ) : Prop :=
  0 < b ∧ (a = 0 ∨ pair (natOrdinal a) (natOrdinal b) ∈ C)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $a,b\in\omega$, put
    $$\RealCutApprox{C}{a}{b}\longleftrightarrow
    0<b\ \land\ (a=0\ \lor\ \langle a,b\rangle\in C).$$
    If $C=\NonnegativeRealCut{r}$ with $r\ge0$, every such fraction satisfies $a/b\le r$.
    For every $\varepsilon>0$ one can choose such a fraction with $r-\varepsilon<a/b$:
    use $0/1$ when $r<\varepsilon$, and otherwise choose a rational strictly between $r-\varepsilon$ and $r$.
-/
lemma cutLowerApproximation_le {r : ℝ} (hr : 0 ≤ r) {a b : ℕ}
    (h : cutLowerApproximation (nonnegativeRealCutCode.{u} r) a b) : (a : ℝ) / b ≤ r := by
  rcases h.2 with rfl | h
  · simpa only [Nat.cast_zero, zero_div] using hr
  · exact ((pair_mem_nonnegativeRealCutCode r a b).mp h).2.le

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $a,b\in\omega$, put
    $$\RealCutApprox{C}{a}{b}\longleftrightarrow
    0<b\ \land\ (a=0\ \lor\ \langle a,b\rangle\in C).$$
    If $C=\NonnegativeRealCut{r}$ with $r\ge0$, every such fraction satisfies $a/b\le r$.
    For every $\varepsilon>0$ one can choose such a fraction with $r-\varepsilon<a/b$:
    use $0/1$ when $r<\varepsilon$, and otherwise choose a rational strictly between $r-\varepsilon$ and $r$.
-/
lemma exists_cutLowerApproximation (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℕ, cutLowerApproximation (nonnegativeRealCutCode.{u} r) a b ∧
      r - ε < (a : ℝ) / b := by
  by_cases h : r < ε
  · exact ⟨0, 1, ⟨by decide, Or.inl rfl⟩, by simpa using sub_neg.mpr h⟩
  · have h0 : 0 ≤ r - ε := sub_nonneg.mpr (le_of_not_gt h)
    obtain ⟨a, b, hb, hl, hu⟩ :=
      (lt_iff_nat_fraction_margin (r - ε) (r - ε / 2) h0).mp (by linarith)
    exact ⟨a, b, ⟨hb, Or.inr ((pair_mem_nonnegativeRealCutCode r a b).mpr ⟨hb, by linarith⟩)⟩, hl⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define $\RealCutSum{C}{D}\IncludedIn\omega\times\omega$ by
    $$\begin{aligned}
    \langle a,b\rangle\in\RealCutSum{C}{D}
    &\longleftrightarrow 0<b\ \land\ \exists c,d,e,f\in\omega\;[\\
    &\qquad\RealCutApprox{C}{c}{d}\ \land\ \RealCutApprox{D}{e}{f}\\
    &\qquad{}\land\ a(df)<(cf+ed)b].
    \end{aligned}$$
    The final inequality says $a/b<c/d+e/f$. All its denominators are positive by the preceding conditions.
-/
lemma rationalSumLess_iff (a b c d e f : ℕ) (hb : 0 < b) (hd : 0 < d) (hf : 0 < f) :
    a * (d * f) < (c * f + e * d) * b ↔ (a : ℝ) / b < (c : ℝ) / d + (e : ℝ) / f := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  rw [div_add_div _ _ (ne_of_gt hd') (ne_of_gt hf'), div_lt_div_iff₀ hb' (mul_pos hd' hf')]
  norm_cast
  rw [Nat.mul_comm d e]

/-- Downward closure of sums of rational lower approximations. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define $\RealCutSum{C}{D}\IncludedIn\omega\times\omega$ by
    $$\begin{aligned}
    \langle a,b\rangle\in\RealCutSum{C}{D}
    &\longleftrightarrow 0<b\ \land\ \exists c,d,e,f\in\omega\;[\\
    &\qquad\RealCutApprox{C}{c}{d}\ \land\ \RealCutApprox{D}{e}{f}\\
    &\qquad{}\land\ a(df)<(cf+ed)b].
    \end{aligned}$$
    The final inequality says $a/b<c/d+e/f$. All its denominators are positive by the preceding conditions.
-/
def sumCutCode (C D : ZFSet.{u}) : ZFSet.{u} :=
  naturalPairSet (fun a b => 0 < b ∧ ∃ c d e f : ℕ,
    cutLowerApproximation C c d ∧ cutLowerApproximation D e f ∧
      a * (d * f) < (c * f + e * d) * b)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For $q=a/b$ with $b>0$, suppose $q<r+s$. Set $\varepsilon=(r+s-q)/3>0$ and choose lower approximations
    $u=c/d$ and $v=e/f$ as above, so that
    $$r-\varepsilon<u\le r,\qquad s-\varepsilon<v\le s.$$
    Then $q<r+s-2\varepsilon<u+v$, giving witnesses to the defining condition.
    Conversely, any witnesses give $q<u+v\le r+s$. This proves equality of the codes; both sides exclude
    zero denominators. Decode arbitrary valid $C,D$ by §{sec:internal-borel-measure-cut} and apply this identity.
    It gives validity and the value of the sum. The final equivalence follows by decoding the code equation
    in one direction and encoding the numerical equation in the other.
-/
lemma fraction_lt_add_iff (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b < r + s ↔ ∃ c d e f : ℕ,
      cutLowerApproximation (nonnegativeRealCutCode.{u} r) c d ∧
      cutLowerApproximation (nonnegativeRealCutCode.{u} s) e f ∧
      a * (d * f) < (c * f + e * d) * b := by
  constructor
  · intro h
    let ε := (r + s - (a : ℝ) / b) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨c, d, hc, hl⟩ := exists_cutLowerApproximation.{u} r hε
    obtain ⟨e, f, he, hk⟩ := exists_cutLowerApproximation.{u} s hε
    refine ⟨c, d, e, f, hc, he, (rationalSumLess_iff a b c d e f hb hc.1 he.1).mpr ?_⟩
    dsimp [ε] at hl hk
    linarith
  · rintro ⟨c, d, e, f, hc, he, hlt⟩
    exact ((rationalSumLess_iff a b c d e f hb hc.1 he.1).mp hlt).trans_le
      (add_le_add (cutLowerApproximation_le hr hc) (cutLowerApproximation_le hs he))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Addition of real cut codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, this definition covers $r=0$, $s=0$, and $r=s=0$ without changing the formula.
    Requiring both approximations to belong to the strict cuts would fail whenever one of these cuts is empty.
-/
theorem sumCutCode_eq (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    sumCutCode (nonnegativeRealCutCode.{u} r) (nonnegativeRealCutCode s) =
      nonnegativeRealCutCode (r + s) := by
  apply naturalPairSet_ext
  intro a b
  exact and_congr_right (fun hb => (fraction_lt_add_iff r s hr hs a b hb).symm)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal addition of real cut codes
-/
theorem sumCutCode_eq_decoded {C D : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) (hD : ValidNonnegativeRealCutCode D) :
    sumCutCode C D = nonnegativeRealCutCode (decodeNonnegativeRealCut C + decodeNonnegativeRealCut D) := by
  calc
    sumCutCode C D = sumCutCode (nonnegativeRealCutCode (decodeNonnegativeRealCut C))
        (nonnegativeRealCutCode (decodeNonnegativeRealCut D)) := congrArg₂ sumCutCode hC.encode_decode hD.encode_decode
    _ = _ := sumCutCode_eq _ _ (decodeNonnegativeRealCut_nonneg hC) (decodeNonnegativeRealCut_nonneg hD)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal addition of real cut codes
-/
theorem sumCutCode_valid {C D : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) (hD : ValidNonnegativeRealCutCode D) :
    ValidNonnegativeRealCutCode (sumCutCode C D) := by
  rw [sumCutCode_eq_decoded hC hD]
  exact nonnegativeRealCutCode_valid _

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal addition of real cut codes
-/
theorem decode_sumCutCode {C D : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) (hD : ValidNonnegativeRealCutCode D) :
    decodeNonnegativeRealCut (sumCutCode C D) = decodeNonnegativeRealCut C + decodeNonnegativeRealCut D := by
  rw [sumCutCode_eq_decoded hC hD, decode_nonnegativeRealCutCode
    (add_nonneg (decodeNonnegativeRealCut_nonneg hC) (decodeNonnegativeRealCut_nonneg hD))]

/-- An equation of valid codes transfers finite additivity to their decoded real values. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus an internal sum equation transfers to an equality of decoded real values.
-/
theorem eq_sumCutCode_iff {C D E : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) (hD : ValidNonnegativeRealCutCode D)
    (hE : ValidNonnegativeRealCutCode E) :
    E = sumCutCode C D ↔ decodeNonnegativeRealCut E = decodeNonnegativeRealCut C + decodeNonnegativeRealCut D := by
  constructor
  · intro h
    rw [h, decode_sumCutCode hC hD]
  · intro h
    rw [sumCutCode_eq_decoded hC hD, ← h]
    exact hE.encode_decode

end PolishSpaceBook.CantorTreeMeasure
