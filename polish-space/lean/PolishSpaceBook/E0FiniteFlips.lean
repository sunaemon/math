module

public import PolishSpaceBook.E0Nonsmooth
public import Mathlib.Data.Finset.SymmDiff

@[expose] public section

/-! # The finite-support XOR action for eventual equality

Finite subsets are supports of the binary direct sum; symmetric difference
is its addition. Its image in permutations of Cantor space is the actual
coordinatewise XOR action, rather than a purely cardinality-based argument.
-/
namespace PolishSpaceBook.E0FiniteFlips
open Set Function
open scoped symmDiff

/-- Toggle exactly the finitely many displayed coordinates. -/
def flip (F : Finset ℕ) (x : cantor_space) : cantor_space :=
  fun n => if n ∈ F then !(x n) else x n

lemma flip_comp (F H : Finset ℕ) (x : cantor_space) :
    flip (F ∆ H) x = flip F (flip H x) := by
  funext n
  by_cases hF : n ∈ F <;> by_cases hH : n ∈ H <;>
    simp [flip, Finset.mem_symmDiff, hF, hH]

/-- Every finite XOR operation is an involutive permutation. -/
def flipEquiv (F : Finset ℕ) : Equiv.Perm cantor_space where
  toFun := flip F
  invFun := flip F
  left_inv x := by funext n; by_cases h : n ∈ F <;> simp [flip, h]
  right_inv x := by funext n; by_cases h : n ∈ F <;> simp [flip, h]

/-- Distinct supports act differently even on the all-zero record. -/
lemma flipEquiv_injective : Injective flipEquiv := by
  intro F H h
  ext n
  have hv := congrFun (congrArg (fun p : Equiv.Perm cantor_space => p (fun _ => false)) h) n
  change (if n ∈ F then true else false) = (if n ∈ H then true else false) at hv
  by_cases hF : n ∈ F <;> by_cases hH : n ∈ H <;> simp_all

/-- The concrete group of finite-support coordinatewise XOR operations. -/
def flipGroup : Subgroup (Equiv.Perm cantor_space) where
  carrier := {p | ∃ F : Finset ℕ, p = flipEquiv F}
  one_mem' := ⟨∅, by ext x n; simp [flipEquiv, flip]⟩
  mul_mem' := by
    rintro p q ⟨F, rfl⟩ ⟨H, rfl⟩
    refine ⟨F ∆ H, ?_⟩
    ext x n
    exact congrFun (flip_comp F H x).symm n
  inv_mem' := by
    rintro p ⟨F, rfl⟩
    exact ⟨F, rfl⟩

instance : Countable flipGroup := by
  classical
  let f : flipGroup → Finset ℕ := fun p => Classical.choose p.property
  have hi : Injective f := by
    intro p q h
    apply Subtype.ext
    calc
      p.val = flipEquiv (f p) := Classical.choose_spec p.property
      _ = flipEquiv (f q) := congrArg flipEquiv h
      _ = q.val := (Classical.choose_spec q.property).symm
  exact hi.countable

/-- The finite-support presentation is faithful and exhausts the acting group. -/
noncomputable def supportEquiv : Finset ℕ ≃ flipGroup :=
  Equiv.ofBijective (fun F => ⟨flipEquiv F, ⟨F, rfl⟩⟩)
    ⟨fun _ _ h => flipEquiv_injective (congrArg Subtype.val h), by
      rintro ⟨p, F, rfl⟩
      exact ⟨F, rfl⟩⟩

/-- Addition in the binary direct-sum presentation is symmetric difference. -/
lemma supportEquiv_symmDiff (F H : Finset ℕ) :
    supportEquiv (F ∆ H) = supportEquiv F * supportEquiv H := by
  apply Subtype.ext
  ext x n
  exact congrFun (flip_comp F H x) n

/-- Eventual equality is exactly having a finite set of disagreements. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Equivalently, $x$ and $y$ may differ, but only in finitely many coordinates.
-/
theorem e0_iff_finite_disagreements (x y : cantor_space) :
    E0 x y ↔ {n | x n ≠ y n}.Finite := by
  constructor
  · rintro ⟨N, hN⟩
    apply (Finset.range N).finite_toSet.subset
    intro n hn
    have hlt : n < N := by
      by_contra h
      exact hn (hN n (by omega))
    exact Finset.mem_range.mpr hlt
  · intro h
    refine ⟨h.toFinset.sup id + 1, ?_⟩
    intro n hn
    by_contra hne
    have hm : n ∈ h.toFinset := h.mem_toFinset.mpr hne
    have hb : n ≤ h.toFinset.sup id := Finset.le_sup (f := id) hm
    omega

/-- Finite changes of a binary record are exactly its finite-XOR orbit. -/
theorem e0_iff_finite_flip (x y : cantor_space) :
    E0 x y ↔ ∃ p : flipGroup, p.val x = y := by
  classical
  constructor
  · rintro ⟨N, hN⟩
    let F := (Finset.range N).filter (fun n => x n ≠ y n)
    refine ⟨⟨flipEquiv F, ⟨F, rfl⟩⟩, ?_⟩
    funext n
    change flip F x n = y n
    by_cases hn : n < N
    · by_cases hxy : x n = y n
      · simp [flip, F, hn, hxy]
      · cases hx : x n <;> cases hy : y n <;> simp_all [flip, F]
    · have hxy := hN n (by omega)
      simp [flip, F, hn, hxy]
  · rintro ⟨⟨p, hp⟩, hxy⟩
    obtain ⟨F, rfl⟩ := hp
    refine ⟨F.sup id + 1, ?_⟩
    intro n hn
    have hnF : n ∉ F := by
      intro h
      have hle : n ≤ F.sup id := Finset.le_sup (f := id) h
      omega
    have h := congrFun hxy n
    simpa [flipEquiv, flip, hnF] using h

/-- The existential description is the canonical subgroup orbit relation. -/
theorem e0_iff_orbit (x y : cantor_space) :
    E0 x y ↔ y ∈ MulAction.orbit flipGroup x := by
  change E0 x y ↔ ∃ p : flipGroup, p.val x = y
  exact e0_iff_finite_flip x y

/-- Each class is the orbit of the countable finite-support XOR group. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Each $\EventualEqualityER$-class is
    therefore a countable
    cloud around one binary sequence, obtained by changing finitely many bits.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Every class is countable: it is the orbit of $x$ under the action of
    $G = \bigoplus_n\ZZ/2\ZZ$ on $\CantorSpace$ by coordinate-wise XOR.
-/
theorem class_eq_countable_flip_orbit (x : cantor_space) :
    {y | E0 x y} = MulAction.orbit flipGroup x ∧
      (MulAction.orbit flipGroup x).Countable := by
  refine ⟨by ext y; exact e0_iff_orbit x y, ?_⟩
  exact countable_range (fun p : flipGroup => p.val x)

end PolishSpaceBook.E0FiniteFlips
