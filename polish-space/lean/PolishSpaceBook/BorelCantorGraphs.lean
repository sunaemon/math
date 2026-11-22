module

public import PolishSpaceBook.BorelPointGraphs
public import PolishSpaceBook.BorelEvaluationPreimage

@[expose] public section

/-! # Internal Cantor space and binary point graphs -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Keep the transitive-model assumptions of §{sec:internal-borel-sets}. Encode each bit by the finite ordinal
    $0$ or $1$, so the graph $g_{i(x)}$ also represents the binary sequence $x$.
-/
def cantorPointGraph (x : ℕ → Bool) : ZFSet.{u} := pointGraph (cantorInclusion x)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every member is the graph of a unique external binary sequence: each value lies in $2=\{0,1\}$.
-/
lemma cantorPointGraph_injective : Function.Injective (cantorPointGraph : (ℕ → Bool) → ZFSet.{u}) :=
  fun _ _ h => cantorInclusion_injective (pointGraph_injective h)

lemma cantorPointGraph_isFunc (x : ℕ → Bool) :
    IsFunc Ordinal.omega0.toZFSet (natOrdinal 2) (cantorPointGraph x : ZFSet.{u}) := by
  refine ⟨?_, (pointGraph_isFunc (cantorInclusion x)).2⟩
  intro p hp
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
  refine ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨i, rfl⟩, ?_⟩
  exact mem_natOrdinal.mpr ⟨(x i).toNat, by cases x i <;> decide, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every member is the graph of a unique external binary sequence: each value lies in $2=\{0,1\}$.
-/
lemma exists_cantorPointGraph_of_isFunc {g : ZFSet.{u}}
    (hg : IsFunc Ordinal.omega0.toZFSet (natOrdinal 2) g) :
    ∃ x : ℕ → Bool, cantorPointGraph x = g := by
  have hvalue (i : ℕ) : ∃ k : Bool, pair (natOrdinal i) (natOrdinal k.toNat) ∈ g := by
    obtain ⟨a, ha, _⟩ := hg.2 _ (mem_omegaOrdinal.mpr ⟨i, rfl⟩)
    obtain ⟨k, hk, rfl⟩ := mem_natOrdinal.mp (ZFSet.pair_mem_prod.mp (hg.1 ha)).2
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨false, ha⟩
    · exact ⟨true, ha⟩
  choose x hx using hvalue
  refine ⟨x, ZFSet.ext fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
    exact hx i
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hg.1 hp)
    obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp ha
    have hb : b = natOrdinal (x i).toNat :=
      (hg.2 _ (mem_omegaOrdinal.mpr ⟨i, rfl⟩)).unique hp (hx i)
    rw [hb]
    exact ZFSet.mem_range.mpr ⟨i, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    The internal function-space construction gives
    $$Y_M:=\funcspace{\omega}{2}\cap M\in M.$$
-/
def internalCantor (M : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.funs Ordinal.omega0.toZFSet (natOrdinal 2) ∩ M

lemma mem_internalCantor {M g : ZFSet.{u}} :
    g ∈ internalCantor M ↔ ∃ x : ℕ → Bool, cantorPointGraph x = g ∧ g ∈ M := by
  rw [internalCantor, ZFSet.mem_inter, ZFSet.mem_funs]
  exact ⟨fun h => (exists_cantorPointGraph_of_isFunc h.1).imp (fun _ he => ⟨he, h.2⟩),
    fun ⟨x, he, hg⟩ => ⟨he ▸ cantorPointGraph_isFunc x, hg⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, every such graph belonging to $M$ is in $Y_M$.
-/
lemma cantorPointGraph_mem_internalCantor {M : ZFSet.{u}} (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalCantor M ↔ cantorPointGraph x ∈ M := by
  rw [internalCantor, ZFSet.mem_inter, ZFSet.mem_funs]
  exact and_iff_right (cantorPointGraph_isFunc x)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The internal function-space construction gives
    $$Y_M:=\funcspace{\omega}{2}\cap M\in M.$$
-/
theorem internalCantor_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    internalCantor M ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  exact internal_funs_mem hM hpair hunion hpower (hsep _) (hsep _) hΩ
    (hM.mem_trans (mem_omegaOrdinal.mpr ⟨2, rfl⟩) hΩ)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    In particular, $Y_M\IncludedIn X_M$.
-/
lemma internalCantor_subset_internalBaire (M : ZFSet.{u}) : internalCantor M ⊆ internalBaire M := by
  intro g hg
  obtain ⟨x, rfl, hx⟩ := mem_internalCantor.mp hg
  exact (pointGraph_mem_internalBaire (cantorInclusion x)).mpr hx

end PolishSpaceBook.BorelExpression
