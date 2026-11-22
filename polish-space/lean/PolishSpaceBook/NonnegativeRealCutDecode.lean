module

public import PolishSpaceBook.NonnegativeRealCutCode

@[expose] public section

/-! # Decoding nonnegative reals from arithmetic conditions on fraction cuts -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels BorelExpression
universe u

/-- Arithmetic cut conditions; no real value is assumed in the definition. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Call a set $C$ a \termdefine{nonnegative real cut code} if it satisfies the following four conditions.
    All variables $a,b,m,d,N$ in these conditions range over $\omega$.

    1. Every member of $C$ is a pair $\Pair{a}{b}$ with $0<b$.
    2. If $0<b$, $0<d$, $ad\le mb$, and $\Pair{m}{d}\in C$, then $\Pair{a}{b}\in C$.
    3. If $\Pair{a}{b}\in C$, there are $m,d$ with $\Pair{m}{d}\in C$ and $ad<mb$.
    4. There is an $N$ such that $\Pair{N}{1}\notin C$.

    The second condition includes equality of fractions, so all representations of the same fraction give the
    same membership answer. The third excludes a largest fraction. The empty code is allowed.
    Write $\RealCutCondition{C}$ for the conjunction of these conditions, with the fixed parameters
    $\omega,G_\times,0,1$ understood.
-/
structure ValidNonnegativeRealCutCode (C : ZFSet.{u}) : Prop where
  typed : ∀ z ∈ C, ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ 0 < b
  lower : ∀ a b m n : ℕ, 0 < b → 0 < n → a * n ≤ m * b →
    pair (natOrdinal m) (natOrdinal n) ∈ C → pair (natOrdinal a) (natOrdinal b) ∈ C
  rounded : ∀ a b : ℕ, pair (natOrdinal a) (natOrdinal b) ∈ C →
    ∃ m n : ℕ, pair (natOrdinal m) (natOrdinal n) ∈ C ∧ a * n < m * b
  bounded : ∃ N : ℕ, pair (natOrdinal N) (natOrdinal 1) ∉ C

lemma ValidNonnegativeRealCutCode.denominator_pos {C : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) {a b : ℕ}
    (h : pair (natOrdinal a) (natOrdinal b) ∈ C) : 0 < b := by
  obtain ⟨m, n, he, hn⟩ := hC.typed _ h
  have hb := natOrdinal_injective (ZFSet.pair_inj.mp he).2
  simpa only [hb] using hn

lemma fraction_le_iff (a b m n : ℕ) (hb : 0 < b) (hn : 0 < n) :
    (a : ℝ) / b ≤ (m : ℝ) / n ↔ a * n ≤ m * b := by
  rw [div_le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)
    (by exact_mod_cast hn : (0 : ℝ) < n)]
  exact_mod_cast Iff.rfl

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Conversely, $\NonnegativeRealCut{r}$ satisfies the first two conditions directly. Rational density supplies
    the larger fraction required in the third condition. Choose an integer $N\ge r$ for the fourth.
    Uniqueness follows from §{sec:internal-borel-measure-cut}, since different nonnegative reals have different
    fraction cuts. In particular, decoding $\NonnegativeRealCut{r}$ returns $r$, including $r=0$.
-/
lemma nonnegativeRealCutCode_valid (r : ℝ) : ValidNonnegativeRealCutCode (nonnegativeRealCutCode.{u} r) := by
  constructor
  · intro z hz
    obtain ⟨a, b, he, hb, _⟩ := (mem_nonnegativeRealCutCode r z).mp hz
    exact ⟨a, b, he, hb⟩
  · intro a b m n hb hn hle hmem
    apply (pair_mem_nonnegativeRealCutCode r a b).mpr
    exact ⟨hb, ((fraction_le_iff a b m n hb hn).mpr hle).trans_lt
      ((pair_mem_nonnegativeRealCutCode r m n).mp hmem).2⟩
  · intro a b hmem
    obtain ⟨hb, hlt⟩ := (pair_mem_nonnegativeRealCutCode r a b).mp hmem
    have hq : 0 ≤ (a : ℝ) / b := by positivity
    obtain ⟨m, n, hn, hqm, hmr⟩ :=
      (lt_iff_nat_fraction_margin ((a : ℝ) / b) (((a : ℝ) / b + r) / 2) hq).mp (by linarith)
    exact ⟨m, n, (pair_mem_nonnegativeRealCutCode r m n).mpr ⟨hn, by linarith⟩,
      (rationalLess_iff a b m n hb hn).mpr hqm⟩
  · obtain ⟨N, hN⟩ := exists_nat_ge r
    refine ⟨N, ?_⟩
    rw [pair_mem_nonnegativeRealCutCode]
    simp only [Nat.cast_one, div_one]
    exact fun h => (not_lt_of_ge hN) h.2

/-- The nonnegative fractions explicitly present in the code. -/
def cutFractionValues (C : ZFSet.{u}) : Set ℝ :=
  {q | ∃ a b : ℕ, pair (natOrdinal a) (natOrdinal b) ∈ C ∧ q = (a : ℝ) / b}

/-- Adjoining zero handles the empty cut, which represents the real zero. -/
def decodeNonnegativeRealCut (C : ZFSet.{u}) : ℝ := sSup (insert 0 (cutFractionValues C))

lemma ValidNonnegativeRealCutCode.bddAbove {C : ZFSet.{u}} (hC : ValidNonnegativeRealCutCode C) :
    BddAbove (insert 0 (cutFractionValues C)) := by
  obtain ⟨N, hN⟩ := hC.bounded
  refine ⟨(N : ℝ), ?_⟩
  intro q hq
  rcases hq with rfl | ⟨a, b, hab, rfl⟩
  · positivity
  · by_contra h
    have hb := hC.denominator_pos hab
    apply hN
    apply hC.lower N 1 a b (by decide) hb
    · apply (fraction_le_iff N 1 a b (by decide) hb).mp
      simpa only [Nat.cast_one, div_one] using (lt_of_not_ge h).le
    · exact hab

lemma decodeNonnegativeRealCut_nonneg {C : ZFSet.{u}} (hC : ValidNonnegativeRealCutCode C) :
    0 ≤ decodeNonnegativeRealCut C := le_csSup hC.bddAbove (Set.mem_insert _ _)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Assume the four conditions. If $\Pair{N}{1}\notin C$, every fraction in the code is strictly less than
    $N$: otherwise the second condition would put $\Pair{N}{1}$ in the code. Thus the displayed set is
    nonempty and bounded above. Its supremum $r$ exists and is nonnegative.
    If $\Pair{a}{b}\in C$, the third condition gives a larger fraction in the code, so $a/b<r$.
    Conversely, if $b>0$ and $a/b<r$, the definition of supremum gives an element of the displayed set strictly
    above $a/b$. This element is not $0$, since $a/b\ge0$, so it comes from a fraction in the code.
    The second condition then gives $\Pair{a}{b}\in C$. The first condition ensures that there are no
    other members, proving $C=\NonnegativeRealCut{r}$.
-/
lemma ValidNonnegativeRealCutCode.mem_iff {C : ZFSet.{u}} (hC : ValidNonnegativeRealCutCode C)
    (a b : ℕ) : pair (natOrdinal a) (natOrdinal b) ∈ C ↔
      0 < b ∧ (a : ℝ) / b < decodeNonnegativeRealCut C := by
  constructor
  · intro hab
    have hb := hC.denominator_pos hab
    obtain ⟨m, n, hmn, hlt⟩ := hC.rounded a b hab
    have hn := hC.denominator_pos hmn
    exact ⟨hb, ((rationalLess_iff a b m n hb hn).mp hlt).trans_le
      (le_csSup hC.bddAbove (Set.mem_insert_of_mem _ ⟨m, n, hmn, rfl⟩))⟩
  · rintro ⟨hb, hlt⟩
    obtain ⟨q, hq, haq⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty 0 _) hlt
    rcases hq with rfl | ⟨m, n, hmn, rfl⟩
    · have hnonneg : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
      exact False.elim ((not_lt_of_ge hnonneg) haq)
    · exact hC.lower a b m n hb (hC.denominator_pos hmn)
        ((fraction_le_iff a b m n hb (hC.denominator_pos hmn)).mp haq.le) hmn

lemma ValidNonnegativeRealCutCode.encode_decode {C : ZFSet.{u}}
    (hC : ValidNonnegativeRealCutCode C) : C = nonnegativeRealCutCode (decodeNonnegativeRealCut C) := by
  ext z
  rw [mem_nonnegativeRealCutCode]
  constructor
  · intro hz
    obtain ⟨a, b, he, _⟩ := hC.typed z hz
    exact ⟨a, b, he, (hC.mem_iff a b).mp (he ▸ hz)⟩
  · rintro ⟨a, b, rfl, hb, hr⟩
    exact (hC.mem_iff a b).mpr ⟨hb, hr⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Decoding arithmetic fraction cuts
-/
theorem validNonnegativeRealCutCode_iff (C : ZFSet.{u}) :
    ValidNonnegativeRealCutCode C ↔ ∃ r : ℝ, 0 ≤ r ∧ C = nonnegativeRealCutCode r := by
  constructor
  · intro hC
    exact ⟨decodeNonnegativeRealCut C, decodeNonnegativeRealCut_nonneg hC, hC.encode_decode⟩
  · rintro ⟨r, _, rfl⟩
    exact nonnegativeRealCutCode_valid r

lemma decode_nonnegativeRealCutCode {r : ℝ} (hr : 0 ≤ r) :
    decodeNonnegativeRealCut (nonnegativeRealCutCode.{u} r) = r := by
  have hC := nonnegativeRealCutCode_valid.{u} r
  apply eq_of_nonneg_fraction_cuts _ r (decodeNonnegativeRealCut_nonneg hC) hr
  intro a b hb
  have h := (hC.mem_iff a b).symm.trans (pair_mem_nonnegativeRealCutCode r a b)
  simpa only [hb, true_and] using h

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Order of nonnegative real codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    An inequality $r\le s$ preserves every strict lower query. If instead $s<r$, a nonnegative rational strictly
    between them belongs to the cut of $r$ and not to the cut of $s$, contradicting inclusion.
    Inclusion of the two internal sets is a bounded predicate, so the shared interpretation theorem also
    proves the internal assertion.
-/
theorem nonnegativeRealCutCode_subset_iff {r s : ℝ} (hs : 0 ≤ s) :
    nonnegativeRealCutCode.{u} r ⊆ nonnegativeRealCutCode s ↔ r ≤ s := by
  constructor
  · intro hsub
    by_contra h
    have hsr := lt_of_not_ge h
    obtain ⟨a, b, hb, hsa, har⟩ :=
      (lt_iff_nat_fraction_margin s ((s + r) / 2) hs).mp (by linarith)
    have ha := (pair_mem_nonnegativeRealCutCode s a b).mp
      (hsub ((pair_mem_nonnegativeRealCutCode r a b).mpr ⟨hb, by linarith⟩))
    linarith
  · intro hrs z hz
    obtain ⟨a, b, rfl, hb, har⟩ := (mem_nonnegativeRealCutCode r z).mp hz
    exact (pair_mem_nonnegativeRealCutCode s a b).mpr ⟨hb, har.trans_le hrs⟩

end PolishSpaceBook.CantorTreeMeasure
