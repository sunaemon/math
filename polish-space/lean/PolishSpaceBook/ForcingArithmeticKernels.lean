module

public import PolishSpaceBook.LambdaArithmeticNormalForm
public import PolishSpaceBook.TreeWellFounded
public import PolishSpaceBook.AnalyticSetsSuslinSchemes

@[expose] public section

/-! # Recursive well-founded trees for real-universal arithmetic kernels

The input is a finite arithmetic formation, whose atomic predicates carry
actual lambda decision programs. Its negation is projected by the proved
normal-form construction. Taking sections retains both the original real
parameter and the fixed first real, using the section lambda program.
-/

noncomputable section
namespace PolishSpaceBook.LambdaTree
open Set

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put the formula in normal form
    $$
    \exists x\,\forall y\,\psi(x,y,a),
    $$
    where $a$ is the real parameter and $\psi$ is arithmetic. For fixed $x$ and $a$, the assertion $\forall y\,\psi(x,y,a)$
    is coanalytic. Equivalently, there is a tree $T_{x,a}$, recursive from $x\oplus a$, such that
    $$
    \forall y\,\psi(x,y,a)
    \quad\Longleftrightarrow\quad
    T_{x,a}\text{ is well-founded}.
    $$
-/
theorem arithmetic_forall_coanalytic {a : ℕ → ℕ} {B : Set (ℕ → ℕ)}
    (hB : ArithmeticalSet a B) :
    CoanalyticSet {x | ∀ y : ℕ → ℕ, pairBaire x y ∈ B} := by
  have hn : FormulaAnalytic a {x | ∃ y, pairBaire x y ∈ Bᶜ} := ⟨Bᶜ, hB.compl, rfl⟩
  unfold CoanalyticSet
  convert hn.projected.analyticSet using 1
  ext x
  simp

/-- No tree presentation or semantic correctness specification is an input. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put the formula in normal form
    $$
    \exists x\,\forall y\,\psi(x,y,a),
    $$
    where $a$ is the real parameter and $\psi$ is arithmetic. For fixed $x$ and $a$, the assertion $\forall y\,\psi(x,y,a)$
    is coanalytic. Equivalently, there is a tree $T_{x,a}$, recursive from $x\oplus a$, such that
    $$
    \forall y\,\psi(x,y,a)
    \quad\Longleftrightarrow\quad
    T_{x,a}\text{ is well-founded}.
    $$
-/
theorem arithmetic_forall_wellFounded_tree {a : ℕ → ℕ} {B : Set (ℕ → ℕ)}
    (hB : ArithmeticalSet a B) :
    ∃ T : PairTree a, ∀ x : ℕ → ℕ,
      (∀ y : ℕ → ℕ, pairBaire x y ∈ B) ↔
        WellFounded (strictTreeExtension (T.section x).tree) := by
  have hn : FormulaAnalytic a {x | ∃ y, pairBaire x y ∈ Bᶜ} :=
    ⟨Bᶜ, hB.compl, rfl⟩
  obtain ⟨T, hT⟩ := hn.projected
  refine ⟨T, fun x => ?_⟩
  have he : (∀ y : ℕ → ℕ, pairBaire x y ∈ B) ↔ x ∉ pairTreeProjection T.tree := by
    rw [← hT]
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
  exact he.trans ((not_mem_pairTreeProjection_iff_section_wellFounded T.tree x).trans
    (prefixTreeWellFounded_iff _ (T.section x).downward))

end PolishSpaceBook.LambdaTree
