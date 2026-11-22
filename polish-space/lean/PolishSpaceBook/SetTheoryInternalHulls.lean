module

public import PolishSpaceBook.SetTheoryRecursiveFormulas

@[expose] public section

/-! # Least internal transitive domains inside a fixed transitive set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Intersection, within A, of the transitive candidates in B that contain a. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    First fix the domain for each input. Put $B=\PowerSet{A}\cap M\in M$, and, for $a\in A$, define
    $$D_a:=\{z\in A:\forall D\in B\,
     ((\mathrm{Trans}(D)\land a\in D)\to z\in D)\}.$$
-/
def transitiveCore (A B a : ZFSet.{u}) : ZFSet.{u} :=
  A.sep (fun z => ∀ D ∈ B, D.IsTransitive → a ∈ D → z ∈ D)

abbrev internalHull (M A a : ZFSet.{u}) : ZFSet.{u} :=
  transitiveCore A (internalPowerSet M A) a

def hullMemberFormula {n : ℕ} (B a z : Fin n) : ForcingFormulas.Formula n :=
  boundedAll B ((transitiveFormula (Fin.last n) ⊓ memberAt a.castSucc (Fin.last n)).imp
    (memberAt z.castSucc (Fin.last n)))

lemma hullMemberFormula_deltaZero {n : ℕ} (B a z : Fin n) : IsDeltaZero (hullMemberFormula B a z) :=
  .all B (((transitiveFormula_deltaZero _).and (memberAt_deltaZero _ _)).imp (memberAt_deltaZero _ _))

/-- The candidate D contains exactly the selected elements of A. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The equality $D=D_a$ is expressed internally by the bounded formula asserting $D\IncludedIn A$ and
    that, for every $z\in A$, membership in $D$ is equivalent to the displayed selection predicate.
-/
def hullFormula {n : ℕ} (A B a D : Fin n) : ForcingFormulas.Formula n :=
  boundedAll D (memberAt (Fin.last n) A.castSucc) ⊓
    boundedAll A ((memberAt (Fin.last n) D.castSucc).iff
      (hullMemberFormula B.castSucc a.castSucc (Fin.last n)))

lemma hullFormula_deltaZero {n : ℕ} (A B a D : Fin n) : IsDeltaZero (hullFormula A B a D) := by
  apply IsDeltaZero.and
  · exact .all D (memberAt_deltaZero _ _)
  · apply IsDeltaZero.all A
    exact ((memberAt_deltaZero _ _).imp (hullMemberFormula_deltaZero _ _ _)).and
      ((hullMemberFormula_deltaZero _ _ _).imp (memberAt_deltaZero _ _))

lemma realize_hullMemberFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (B a z : Fin n) (xs : Fin n → ClassDomain C) :
    (hullMemberFormula B a z).Realize Empty.elim xs ↔
      ∀ D ∈ (xs B).val, D.IsTransitive → (xs a).val ∈ D → (xs z).val ∈ D := by
  simp only [hullMemberFormula, realize_boundedAll, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, realize_transitiveFormula C hC, realize_memberAt_class,
    Fin.snoc_last, Fin.snoc_castSucc, and_imp]
  constructor
  · intro h D hD
    exact h ⟨D, hC _ (xs B).property _ hD⟩ hD
  · intro h D hD
    exact h D.val hD

lemma realize_hullFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (A B a D : Fin n) (xs : Fin n → ClassDomain C) :
    (hullFormula A B a D).Realize Empty.elim xs ↔
      (xs D).val = transitiveCore (xs A).val (xs B).val (xs a).val := by
  simp only [hullFormula, BoundedFormula.realize_inf, realize_boundedAll, BoundedFormula.realize_iff,
    realize_memberAt_class, realize_hullMemberFormula C hC, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨hsub, heq⟩
    apply ZFSet.ext
    intro z
    rw [transitiveCore, ZFSet.mem_sep]
    constructor
    · intro hz
      let zC : ClassDomain C := ⟨z, hC _ (xs D).property _ hz⟩
      have hzA := hsub zC hz
      exact ⟨hzA, (heq zC hzA).mp hz⟩
    · rintro ⟨hzA, hz⟩
      exact (heq ⟨z, hC _ (xs A).property _ hzA⟩ hzA).mpr hz
  · intro he
    constructor
    · intro z hz
      rw [he] at hz
      exact (ZFSet.mem_sep.mp hz).1
    · intro z hzA
      rw [he, transitiveCore, ZFSet.mem_sep]
      exact and_iff_right hzA

lemma realize_hullMemberFormula_set (M : ZFSet.{u}) (hM : M.IsTransitive)
    {n : ℕ} (B a z : Fin n) (xs : Fin n → M) :
    (hullMemberFormula B a z).Realize Empty.elim xs ↔
      ∀ D ∈ (xs B).val, D.IsTransitive → (xs a).val ∈ D → (xs z).val ∈ D :=
  realize_hullMemberFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) B a z xs

lemma realize_hullFormula_set (M : ZFSet.{u}) (hM : M.IsTransitive)
    {n : ℕ} (A B a D : Fin n) (xs : Fin n → M) :
    (hullFormula A B a D).Realize Empty.elim xs ↔
      (xs D).val = transitiveCore (xs A).val (xs B).val (xs a).val :=
  realize_hullFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) A B a D xs

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    It contains $a$, is a subset of $A$, and is transitive: if $z\in D_a$ and $w\in z$, then
    $w\in A$, and every transitive candidate containing $a$ contains $z$ and hence $w$.
-/
lemma internalHull_subset (M A a : ZFSet.{u}) : internalHull M A a ⊆ A :=
  fun _ hz => (ZFSet.mem_sep.mp hz).1

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    It contains $a$, is a subset of $A$, and is transitive: if $z\in D_a$ and $w\in z$, then
    $w\in A$, and every transitive candidate containing $a$ contains $z$ and hence $w$.
-/
lemma mem_internalHull {M A a : ZFSet.{u}} (ha : a ∈ A) : a ∈ internalHull M A a :=
  ZFSet.mem_sep.mpr ⟨ha, fun _ _ _ h => h⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    It contains $a$, is a subset of $A$, and is transitive: if $z\in D_a$ and $w\in z$, then
    $w\in A$, and every transitive candidate containing $a$ contains $z$ and hence $w$.
-/
lemma internalHull_transitive {M A a : ZFSet.{u}} (hA : A.IsTransitive) :
    (internalHull M A a).IsTransitive := by
  intro z hz w hw
  obtain ⟨hzA, hz⟩ := ZFSet.mem_sep.mp hz
  exact ZFSet.mem_sep.mpr ⟨hA.mem_trans hw hzA, fun D hD hDt haD => hDt.mem_trans hw (hz D hD hDt haD)⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    It is also minimal among internal transitive subsets of $A$ containing $a$:
    $$D\in M,\quad D\IncludedIn A,\quad\mathrm{Trans}(D),\quad a\in D
    \quad\Longrightarrow\quad D_a\IncludedIn D.$$
-/
lemma internalHull_minimal {M A a D : ZFSet.{u}} (hD : D ∈ M) (hDA : D ⊆ A)
    (hDt : D.IsTransitive) (haD : a ∈ D) : internalHull M A a ⊆ D := by
  intro z hz
  exact (ZFSet.mem_sep.mp hz).2 D (ZFSet.mem_sep.mpr ⟨hD, hDA⟩) hDt haD

/-- Internal Power Set bounds the candidate domains; bounded Separation takes their intersection. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The displayed predicate is bounded, so Separation gives $D_a\in M$.
-/
theorem internalHull_mem {M A a : ZFSet.{u}} (hM : M.IsTransitive)
    (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence (hullMemberFormula (0 : Fin 3) 1 2))
    (hA : A ∈ M) (ha : a ∈ M) : internalHull M A a ∈ M := by
  let B := internalPowerSet M A
  have hB : B ∈ M := internalPowerSet_mem hM hpower hA
  apply separation_mem_of_absolute hM (hullMemberFormula (0 : Fin 3) 1 2) hsep
    ![⟨B, hB⟩, ⟨a, ha⟩] hA
  intro z _
  simpa [Fin.snoc, B] using
    realize_hullMemberFormula_set M hM (0 : Fin 3) 1 2 (Fin.snoc ![⟨B, hB⟩, ⟨a, ha⟩] z)

end PolishSpaceBook.SetTheoryModels
