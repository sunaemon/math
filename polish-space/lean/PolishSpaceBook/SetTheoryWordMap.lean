module

public import PolishSpaceBook.SetTheoryWordOperations

@[expose] public section

/-! # Coordinatewise maps of finite graphs inside a transitive model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Applying a numerical graph to every coordinate, retaining the domain. -/
def SetWordMap (Ω G s t : ZFSet.{u}) : Prop :=
  ∀ i ∈ Ω, ∀ v ∈ Ω, pair i v ∈ t ↔ ∃ w ∈ Ω, pair i w ∈ s ∧ pair w v ∈ G

/-- Parameters omega, numerical graph, source word, target word. -/
def wordMapPredicate : BoundedSetPredicate 4 :=
  .all 0 (.all 0 (.iff (.pairMember 3 4 5) (.ex 0 (.conj (.pairMember 2 4 6) (.pairMember 1 6 5)))))

def wordMapFormula : ForcingFormulas.Formula 4 := wordMapPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Apply the uniform interpretation principle.
-/
lemma realize_wordMapFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω G s t : M) :
    wordMapFormula.Realize Empty.elim ![Ω, G, s, t] ↔ SetWordMap Ω.val G.val s.val t.val :=
  wordMapPredicate.realize_compile hM ![Ω, G, s, t]

lemma pair_mem_wordGraph_map (f : ℕ → ℕ) (s : List ℕ) (i v : ℕ) :
    pair (natOrdinal i) (natOrdinal v) ∈ (wordGraph (s.map f) : ZFSet.{u}) ↔
      ∃ w : ℕ, pair (natOrdinal i) (natOrdinal w) ∈ (wordGraph s : ZFSet.{u}) ∧ v = f w := by
  simp only [pair_mem_wordGraph, List.length_map, List.getElem_map]
  constructor
  · rintro ⟨hi, hv⟩
    exact ⟨s[i], ⟨hi, rfl⟩, hv.symm⟩
  · rintro ⟨w, ⟨hi, hw⟩, hv⟩
    exact ⟨hi, by rw [hw, hv]⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Coordinatewise finite-word maps
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    At each coordinate of the source word, its unique value is the witness for the numerical graph, whose unique
    output is the target value. Outside the source domain there is no such witness. Thus the pair-membership
    conditions are precisely those of the coordinatewise image.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    In particular, the two numerical projection graphs constructed in §{sec:internal-natural-arithmetic} give the
    two projected words used by the counterexample tree.
-/
lemma setWordMap_iff (f : ℕ → ℕ) (s t : List ℕ) :
    SetWordMap.{u} Ordinal.omega0.toZFSet (sequenceGraph (fun n => natOrdinal (f n)))
      (wordGraph s) (wordGraph t) ↔ t = s.map f := by
  simp only [SetWordMap, forall_mem_omegaOrdinal.{u}, exists_mem_omegaOrdinal.{u},
    pair_mem_sequenceGraph, natOrdinal_injective.{u}.eq_iff]
  constructor
  · intro h
    exact wordGraph_ext.{u} (fun i v => (h i v).trans (pair_mem_wordGraph_map.{u} f s i v).symm)
  · rintro rfl
    exact pair_mem_wordGraph_map.{u} f s

end PolishSpaceBook.SetTheoryModels
