module

public import PolishSpaceBook.BorelCylinderLimits
public import PolishSpaceBook.BorelInternalLeafFamilies

@[expose] public section

/-! # Whole internal code families for selected cylinders

A set of selected numerical indices supplies one bounded definition of the
entire sequence of leaf-or-empty label graphs. Replacement collects that
sequence before the countable-union constructor is used. The index set must
itself be constructed internally by the caller.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
open NamedLambda
open scoped Classical
universe u

/-- Parameters of leafGraphPredicate, selected indices, empty graph, input, output. -/
def selectedLeafSequencePredicate : BoundedSetPredicate 10 :=
  .disj (.conj (.member 8 6) (leafGraphPredicate.rename ![0, 1, 2, 3, 4, 5, 8, 9]))
    (.conj (.neg (.member 8 6)) (.equal 9 7))

lemma eval_selectedLeafSequencePredicate (D : ZFSet.{u}) (n : ℕ) (L : ZFSet.{u}) :
    selectedLeafSequencePredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
      naturalBinaryGraph (fun a b => a + b), natOrdinal 3, D, Code.empty.val.labelGraph, natOrdinal n, L] ↔
      L = (if natOrdinal n ∈ D then Code.leaf n else Code.empty).val.labelGraph := by
  change ((natOrdinal n ∈ D ∧
    leafGraphPredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
      naturalBinaryGraph (fun a b => a + b), natOrdinal 3, natOrdinal n, L]) ∨
    (natOrdinal n ∉ D ∧ L = Code.empty.val.labelGraph)) ↔ _
  rw [eval_leafGraphPredicate]
  by_cases h : natOrdinal n ∈ D <;> simp [h, Code.leaf]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep

theorem selectedLeafFamily_labelGraphs_mem (D : ZFSet.{u}) (hD : D ∈ M) :
    sequenceGraph (fun n => (if natOrdinal n ∈ D then Code.leaf n else Code.empty).val.labelGraph) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let W : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let e : M := ⟨_, hM.mem_trans (mem_finiteSequences.mpr ⟨[], rfl⟩) W.property⟩
  have hempty : (Code.empty.val.labelGraph : ZFSet.{u}) ∈ M :=
    Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
      (basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep 0)
  let ps : Fin 8 → M := ![Ω, W, e, ⟨_, hn 0⟩,
    ⟨_, naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩, ⟨_, hn 3⟩, ⟨_, hD⟩, ⟨_, hempty⟩]
  let values (n : ℕ) : M := ⟨(if natOrdinal n ∈ D then Code.leaf n else Code.empty).val.labelGraph, by
    split_ifs
    · exact basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep n
    · exact hempty⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep selectedLeafSequencePredicate ps values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
        naturalBinaryGraph (fun a b => a + b), natOrdinal 3, D, Code.empty.val.labelGraph, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_selectedLeafSequencePredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem Code.selectedCylinders_labelGraph_mem (P : List ℕ → Prop)
    (D : ZFSet.{u}) (hD : D ∈ M) (hspec : ∀ n, natOrdinal n ∈ D ↔ P (NatListCode.decode n)) :
    (Code.selectedCylinders P).val.labelGraph ∈ M := by
  apply Code.iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep
  have h := selectedLeafFamily_labelGraphs_mem hM hinf hpair hunion hpower hsep hrep D hD
  simpa only [hspec] using h

end PolishSpaceBook.BorelExpression
