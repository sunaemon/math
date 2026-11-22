module

public import PolishSpaceBook.BorelInternalParameters
public import PolishSpaceBook.SetTheoryFunctionClosure

@[expose] public section

/-! # Baire points as the actual functions on the internal natural numbers -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

lemma pointGraph_isFunc (x : ℕ → ℕ) :
    IsFunc Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet (pointGraph x : ZFSet.{u}) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr
      ⟨mem_omegaOrdinal.mpr ⟨i, rfl⟩, mem_omegaOrdinal.mpr ⟨x i, rfl⟩⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp ha
    refine ⟨natOrdinal (x i), (pair_mem_pointGraph x i (x i)).mpr rfl, ?_⟩
    intro b hb
    obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hb
    obtain ⟨hi, hv⟩ := ZFSet.pair_inj.mp hj
    exact (congrArg (fun k => natOrdinal (x k)) (natOrdinal_injective hi)).symm.trans hv |>.symm

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every $g\in X_M$ is $g_x$ for a unique external sequence $x$: its value at the finite ordinal $n$
    is a unique finite ordinal, which specifies $x(n)$. Conversely, every $g_x\in M$ belongs to $X_M$.
    Thus $X_M$ consists exactly of the point graphs available in $M$.
-/
lemma pointGraph_injective : Function.Injective (pointGraph : (ℕ → ℕ) → ZFSet.{u}) := by
  intro x y h
  funext i
  have hx : pair (natOrdinal i) (natOrdinal (x i)) ∈ (pointGraph y : ZFSet.{u}) :=
    h ▸ (pair_mem_pointGraph x i (x i)).mpr rfl
  exact ((pair_mem_pointGraph y i (x i)).mp hx).symm

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every $g\in X_M$ is $g_x$ for a unique external sequence $x$: its value at the finite ordinal $n$
    is a unique finite ordinal, which specifies $x(n)$. Conversely, every $g_x\in M$ belongs to $X_M$.
    Thus $X_M$ consists exactly of the point graphs available in $M$.
-/
lemma exists_pointGraph_of_isFunc {g : ZFSet.{u}}
    (hg : IsFunc Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet g) :
    ∃ x : ℕ → ℕ, pointGraph x = g := by
  have hvalue (i : ℕ) : ∃ k, pair (natOrdinal i) (natOrdinal k) ∈ g := by
    obtain ⟨b, hb, _⟩ := hg.2 _ (mem_omegaOrdinal.mpr ⟨i, rfl⟩)
    obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp (ZFSet.pair_mem_prod.mp (hg.1 hb)).2
    exact ⟨k, hb⟩
  choose x hx using hvalue
  refine ⟨x, ZFSet.ext fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
    exact hx i
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hg.1 hp)
    obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp ha
    have hb : b = natOrdinal (x i) :=
      (hg.2 _ (mem_omegaOrdinal.mpr ⟨i, rfl⟩)).unique hp (hx i)
    rw [hb]
    exact (pair_mem_pointGraph x i (x i)).mpr rfl

/-- The model's reals, rather than all external reals. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    The internal function-space construction gives
    $$X_M:=\funcspace{\omega}{\omega}\cap M\in M,$$
    where functions in this formula are sets of ordered pairs.
-/
def internalBaire (M : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.funs Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet ∩ M

lemma mem_internalBaire {M g : ZFSet.{u}} :
    g ∈ internalBaire M ↔ ∃ x : ℕ → ℕ, pointGraph x = g ∧ g ∈ M := by
  rw [internalBaire, ZFSet.mem_inter, ZFSet.mem_funs]
  exact ⟨fun h => (exists_pointGraph_of_isFunc h.1).imp (fun _ he => ⟨he, h.2⟩),
    fun ⟨x, he, hg⟩ => ⟨he ▸ pointGraph_isFunc x, hg⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every $g\in X_M$ is $g_x$ for a unique external sequence $x$: its value at the finite ordinal $n$
    is a unique finite ordinal, which specifies $x(n)$. Conversely, every $g_x\in M$ belongs to $X_M$.
    Thus $X_M$ consists exactly of the point graphs available in $M$.
-/
lemma pointGraph_mem_internalBaire {M : ZFSet.{u}} (x : ℕ → ℕ) :
    pointGraph x ∈ internalBaire M ↔ pointGraph x ∈ M := by
  rw [internalBaire, ZFSet.mem_inter, ZFSet.mem_funs]
  exact and_iff_right (pointGraph_isFunc x)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The internal function-space construction gives
    $$X_M:=\funcspace{\omega}{\omega}\cap M\in M,$$
    where functions in this formula are sets of ordered pairs.
-/
theorem internalBaire_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    internalBaire M ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  exact internal_funs_mem hM hpair hunion hpower (hsep _) (hsep _) hΩ hΩ

end PolishSpaceBook.BorelExpression
