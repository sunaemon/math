module

public import PolishSpaceBook.LambdaEffectiveBoundedness
public import PolishSpaceBook.LambdaContinuousCoding

@[expose] public section

namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
open LambdaRelative
local instance : Encodable (List ℕ) := NatListCode.encodable
local instance : Encodable (List ℕ × List ℕ) := wordPairEncodable
attribute [local instance] Classical.propDecidable

/-- The characteristic name of a rooted tree, including its empty root. -/
noncomputable def treeCharacteristic (T : RootedPrefixTree) (n : ℕ) : ℕ :=
  if NatListCode.decode n ∈ T.tree then 1 else 0

theorem treeFromCode_characteristic (T : RootedPrefixTree) :
    treeFromCode (treeCharacteristic T) = T := by
  have he : (treeFromCode (treeCharacteristic T)).tree = T.tree := by
    ext t
    constructor
    · intro h
      by_cases ht : t = []
      · simpa [ht] using T.root_mem
      · have hm := h t.length (List.length_pos_iff.mpr ht) le_rfl
        simpa [treeCharacteristic] using hm
    · intro ht j _ _
      simp [treeCharacteristic, T.downward ht (List.take_prefix j t)]
  have ext : ∀ U V : RootedPrefixTree, U.tree = V.tree → U = V := by
    rintro ⟨u, hu, hru⟩ ⟨v, hv, hrv⟩ rfl
    rfl
  exact ext _ _ he

noncomputable def rootedSectionCode {ε : ℕ → ℕ} (T : PairTree ε) (x : ℕ → ℕ) : ℕ → ℕ :=
  treeCharacteristic (rootedSection T x)

def rootSelector : AlphaTerm := numericalIfLe (numericalProjectionTerm true)
  (numericalConstant 0) (numericalConstant 1) (numericalProjectionTerm false)

theorem rootSelector_computes : NumericalComputes rootSelector
    (fun z => if z.unpair.1 ≤ 0 then 1 else z.unpair.2) :=
  (projection_computes true).ifLe (numericalConstant_computes 0)
    (numericalConstant_computes 1) (projection_computes false)

/-- The same finite term reads every section. It corrects just the empty-root bit. -/
def rootedSectionCodeProgram (P : AlphaTerm) : AlphaTerm :=
  mapOutputProgram rootSelector (pairOutputProgram (liftNumericalProgram numericalIdentity)
    (relativeComposeProgram (compositionProgram P (parameterProjectionProgram true)) sectionInputProgram))

theorem rootedSectionCodeProgram_computes {ε : ℕ → ℕ} (T : PairTree ε)
    {P : AlphaTerm} (hP : Decides ε P (· ∈ T.tree)) (x : ℕ → ℕ) :
    Computes (pairBaire ε x) (rootedSectionCodeProgram P) (rootedSectionCode T x) := by
  have hleft : Computes (sectionParameter ε x) (parameterProjectionProgram true) ε :=
    parameterProjection_computes true ε x
  have hraw := (hP.changeParameter hleft).precomp (sectionInput_computes ε x)
  have hid := numericalIdentity_computes.uniform
  refine ⟨mapOutputProgram_closed rootSelector_computes.1
    (pairOutputProgram_closed hid.1 hraw.1), ?_⟩
  intro n
  have hr := hraw.runs (NatListCode.decode n)
  simp only [Encodable.encode, NatListCode.encode_decode] at hr
  have hout := mapOutputProgram_runs rootSelector_computes.1
    (pairOutputProgram_closed hid.1 hraw.1)
    (pairOutputProgram_runs hid.1 hraw.1 (hid.2 (sectionParameter ε x) n) hr)
    (rootSelector_computes.2 (Nat.pair n
      (if (seqPrefix x (NatListCode.decode n).length, NatListCode.decode n) ∈ T.tree then 1 else 0)))
  have hδ : sectionParameter ε x = pairBaire ε x := by funext k; rfl
  rw [hδ] at hout
  simpa only [rootedSectionCodeProgram, rootSelector, rootedSectionCode, treeCharacteristic,
    rootedSection, mem_ofPred_eq, Nat.unpair_pair, Nat.le_zero_eq, decode_eq_nil_iff,
    ite_or, ite_true, sectionParameter, pairBaire, Encodable.encode, id_eq] using hout

theorem rootedSectionCode_continuous {ε : ℕ → ℕ} (T : PairTree ε) :
    Continuous (rootedSectionCode T) := by
  obtain ⟨P, hP⟩ := T.decidable
  have hc := LambdaContinuousCode.continuous_of_parameter (D := Set.univ)
    (F := fun x => rootedSectionCode T x.val) ε (rootedSectionCodeProgram P)
    (fun x n => by
      have hδ : typeTwoPairName ε x.val = pairBaire ε x.val := by funext k; rfl
      rw [hδ]
      simpa only [typeTwoPairName, pairBaire, Encodable.encode, id_eq] using
        (rootedSectionCodeProgram_computes T hP x.val).2 n)
  exact hc.comp (continuous_id.subtype_mk (fun _ => Set.mem_univ _))

def WellFoundedTreeCodes : Set (ℕ → ℕ) :=
  {p | WellFounded (strictTreeExtension (treeFromCode p).tree)}

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    so it is $\lPi^1_1$.
-/
theorem complement_wellFoundedTreeCodes_projected (ε : ℕ → ℕ) :
    Projected ε WellFoundedTreeCodesᶜ := by
  refine ⟨delayedBranchTree ε, ?_⟩
  ext p
  exact (delayedBranchTree_projection ε p).symm

theorem rootedSectionCode_reduces {ε : ℕ → ℕ} (T : PairTree ε) (x : ℕ → ℕ) :
    rootedSectionCode T x ∈ WellFoundedTreeCodes ↔ x ∉ pairTreeProjection T.tree := by
  change WellFounded (strictTreeExtension
    (treeFromCode (treeCharacteristic (rootedSection T x))).tree) ↔ _
  rw [treeFromCode_characteristic]
  rw [← branch_rootedSection_iff T x,
    ← prefixTreeWellFounded_iff _ (rootedSection T x).downward]
  simp only [PrefixTreeWellFounded, not_exists]

/-- Each side of the reduction is tested using the actual code and no branch choice. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Membership in $\WellFoundedTrees$ says
    $$\forall x\in\BaireSpace\;\exists n\;\restrict{x}{n}\notin T_p,$$
-/
theorem wellFoundedTreeCodes_iff (p : ℕ → ℕ) :
    p ∈ WellFoundedTreeCodes ↔
      ∀ x : ℕ → ℕ, ∃ n, seqPrefix x n ∉ (treeFromCode p).tree := by
  change WellFounded (strictTreeExtension (treeFromCode p).tree) ↔ _
  rw [← prefixTreeWellFounded_iff _ (treeFromCode p).downward]
  simp only [PrefixTreeWellFounded, treeBody, mem_ofPred_eq, not_exists, not_forall]

/-- The section-code reduction is realized by one term with the original
parameter joined to its varying input; no new real parameter is introduced. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For lightface data the map is recursive without an extra parameter. Hence $\WellFoundedTrees$ is
    \termuseas{Gamma-complete}{$\bPi^1_1$-complete}, and the reduction is effective in the lightface case.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Every $\lPi^1_1$ set admits such a rank. Indeed, reduce $A$ recursively, and hence continuously, to
    $\WellFoundedTrees$: choose a recursive map $x\mapsto T_x$ such that
    $$x\in A \quad\Longleftrightarrow\quad T_x\in\WellFoundedTrees.$$
-/
theorem relative_wellFounded_reduction {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε Aᶜ) :
    ∃ (f : (ℕ → ℕ) → (ℕ → ℕ)) (P : AlphaTerm), Continuous f ∧
      (∀ x, Computes (pairBaire ε x) P (f x)) ∧
      ∀ x, x ∈ A ↔ f x ∈ WellFoundedTreeCodes := by
  obtain ⟨T, hT⟩ := hA
  obtain ⟨P, hP⟩ := T.decidable
  refine ⟨rootedSectionCode T, rootedSectionCodeProgram P,
    rootedSectionCode_continuous T, rootedSectionCodeProgram_computes T hP, ?_⟩
  intro x
  rw [rootedSectionCode_reduces, ← hT]
  exact not_not.symm

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Conversely, let $A\IncludedIn\BaireSpace$ be $\bPi^1_1$. Apply the pair-tree representation
    of §{sec:edst-recursive-trees}, relative to a code for its complement, to obtain a tree $S$ such that
    $$p\notin A\quad\Longleftrightarrow\quad
    \exists q\;\forall n\;(\restrict{p}{n},\restrict{q}{n})\in S.$$
    Put $V_p=\{t:(\restrict{p}{|t|},t)\in S\}$, adding the empty root if necessary; this does not add any infinite
    branch. Let $c(p)$ be its characteristic code under the preceding convention, so $T_{c(p)}=V_p$.
    Each membership test uses only a finite prefix of the input, so $p\mapsto c(p)$ is continuous and recursive
    relative to the chosen code. The section-tree test gives
    $$p\in A\quad\Longleftrightarrow\quad c(p)\in\WellFoundedTrees.$$
-/
theorem coanalytic_continuous_reduction {A : Set (ℕ → ℕ)} (hA : AnalyticSet Aᶜ) :
    ∃ f : (ℕ → ℕ) → (ℕ → ℕ), Continuous f ∧
      ∀ x, x ∈ A ↔ f x ∈ WellFoundedTreeCodes := by
  obtain ⟨ε, T, hT⟩ := (analyticSet_iff_exists_parameter Aᶜ).mp hA
  refine ⟨rootedSectionCode T, rootedSectionCode_continuous T, ?_⟩
  intro x
  rw [rootedSectionCode_reduces, ← hT]
  exact not_not.symm

end LambdaTree
end PolishSpaceBook
