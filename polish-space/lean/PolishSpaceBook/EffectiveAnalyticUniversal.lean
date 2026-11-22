module

public import PolishSpaceBook.LambdaIndexedTrees
public import PolishSpaceBook.LambdaBairePreimages
public import PolishSpaceBook.LambdaArithmeticNormalForm
public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies

@[expose] public section

/-! # Effective analytic universality and the first-coordinate diagonal

A natural-number parameter is coded by the first left digit of a paired
Baire name. The delayed indexed trees provide total membership tests even
for indices of partial programs. Every construction keeps the same oracle.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance analyticUniversalListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance analyticUniversalPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- The universal family has natural-number indices, rather than real parameters. -/
def effectiveAnalyticUniversal (ε : ℕ → ℕ) : Set (ℕ × (ℕ → ℕ)) :=
  {z | z.2 ∈ indexedProjection ε z.1}

/-- Read the index from the first left digit, and retain the right point. -/
def analyticUniversalNodes (ε : ℕ → ℕ) : Set (List ℕ × List ℕ) :=
  {z | (rightWitness z.1, z.2) ∈ indexedNodes ε (z.1.headD 0).unpair.1}

/-- A numerical lambda transformation supplies the index and the two words to
one fixed family decider. -/
theorem analyticUniversalNodes_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (· ∈ analyticUniversalNodes ε) := by
  have hh : NumericalComputes (listFieldTerm true)
      (fun r => (NatListCode.decode r).headD 0) :=
    ⟨listFieldTerm_closed true, fun r => by
      simpa only [NatListCode.encode_decode, List.headD_eq_getD]
        using listHead_code (NatListCode.decode r)⟩
  have h := ((projection_computes true).comp (hh.comp (projection_computes true))).pair
    (((witnessProjection_computes false).comp (projection_computes true)).pair
      (projection_computes false))
  exact (indexedTree_family_decidable ε).precompNumerical
    (g := fun z : List ℕ × List ℕ =>
      ((z.1.headD 0).unpair.1, (rightWitness z.1, z.2))) h
    (fun z => by simp [Encodable.encode, Encodable.encodeSigma, rightWitness])

/-- At length zero no index is read and the empty indexed node always passes. -/
def analyticUniversalTree (ε : ℕ → ℕ) : PairTree ε where
  tree := analyticUniversalNodes ε
  synchronized := by
    intro z hz
    simpa [rightWitness] using hz.1
  downward := by
    intro z hz n
    cases n with
    | zero => simp [analyticUniversalNodes, indexedNodes, rightWitness]
    | succ n =>
      have hh : (z.1.take (n+1)).headD 0 = z.1.headD 0 := by
        cases z.1 <;> simp
      have h := indexedNodes_downward ε _ hz (n+1)
      simpa only [analyticUniversalNodes, mem_ofPred_eq, hh, rightWitness, List.map_take] using h
  decidable := analyticUniversalNodes_decidable ε

/-- Beyond the empty prefix, the first left digit fixes the section index. -/
theorem analyticUniversalTree_body (ε : ℕ → ℕ) (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody (analyticUniversalTree ε).tree ↔
      (rightBaire x,q) ∈ pairTreeBody (indexedTree ε (leftBaire x 0)).tree := by
  have hmap (n : ℕ) : rightWitness (seqPrefix x n) = seqPrefix (rightBaire x) n := by
    simp [rightWitness, rightBaire, seqPrefix, List.map_ofFn, Function.comp_def]
  have hhead (n : ℕ) : (seqPrefix x (n+1)).headD 0 = x 0 := by
    simp [seqPrefix, List.ofFn_succ]
  constructor
  · intro h n
    cases n with
    | zero => simp [indexedTree, indexedNodes, seqPrefix]
    | succ n =>
      have hn := h (n+1)
      change (rightWitness (seqPrefix x (n+1)),seqPrefix q (n+1)) ∈
        indexedNodes ε ((seqPrefix x (n+1)).headD 0).unpair.1 at hn
      simpa only [hmap, hhead, leftBaire, indexedTree] using hn
  · intro h n
    cases n with
    | zero => simp [analyticUniversalTree, analyticUniversalNodes, indexedNodes, seqPrefix, rightWitness]
    | succ n =>
      change (rightWitness (seqPrefix x (n+1)),seqPrefix q (n+1)) ∈
        indexedNodes ε ((seqPrefix x (n+1)).headD 0).unpair.1
      simpa only [hmap, hhead, leftBaire, indexedTree] using h (n+1)

/-- The product family is effectively analytic in the paired-name presentation. -/
theorem effectiveAnalyticUniversal_projected (ε : ℕ → ℕ) :
    Projected ε {x | (leftBaire x 0, rightBaire x) ∈ effectiveAnalyticUniversal ε} := by
  refine ⟨analyticUniversalTree ε, ?_⟩
  ext x
  change (∃ q, (rightBaire x,q) ∈ pairTreeBody (indexedTree ε (leftBaire x 0)).tree) ↔ _
  simp only [pairTreeProjection, mem_ofPred_eq, analyticUniversalTree_body]

/-- Every section is relatively effectively analytic. -/
theorem effectiveAnalyticUniversal_section (ε : ℕ → ℕ) (e : ℕ) :
    Projected ε {p | (e,p) ∈ effectiveAnalyticUniversal ε} :=
  ⟨indexedTree ε e, rfl⟩

/-- The normal form and delayed total family cover all relatively analytic sets. -/
theorem effectiveAnalyticUniversal_universal (ε : ℕ → ℕ) (A : Set (ℕ → ℕ))
    (hA : Projected ε A) :
    ∃ e, A = {p | (e,p) ∈ effectiveAnalyticUniversal ε} :=
  (projected_iff_index ε A).mp hA

/-- Pair the first point digit, repeated as a name of the discrete index, with
all the point digits. The fixed parameter is discarded only by projections. -/
def analyticDiagonalProgram : AlphaTerm := pairOutputProgram
  (mapOutputProgram (numericalProjectionTerm false) (queryOutputProgram (constantProgram 0)))
  (mapOutputProgram (numericalProjectionTerm false)
    (queryOutputProgram (liftNumericalProgram numericalIdentity)))

theorem analyticDiagonalProgram_runs (ε p : ℕ → ℕ) (n : ℕ) :
    OracleRuns (pairBaire ε p) analyticDiagonalProgram n (Nat.pair (p 0) (p n)) := by
  have h := ((uniform_constant 0).query.map (projection_computes false)).pair
    (numericalIdentity_computes.uniform.query.map (projection_computes false))
  simpa [analyticDiagonalProgram, pairBaire] using h.2 (pairBaire ε p) n

/-- The complement of the first-coordinate diagonal is a recursive inverse image. -/
theorem effectiveAnalyticUniversal_diagonalPreimage (ε : ℕ → ℕ) :
    Projected ε {p | (p 0,p) ∈ effectiveAnalyticUniversal ε} := by
  have hclosed : analyticDiagonalProgram.Closed :=
    (((uniform_constant 0).query.map (projection_computes false)).pair
      (numericalIdentity_computes.uniform.query.map (projection_computes false))).1
  have h := (effectiveAnalyticUniversal_projected ε).computablePreimage hclosed
    (F := fun p => pairBaire (fun _ => p 0) p) (analyticDiagonalProgram_runs ε)
  simpa only [preimage_ofPred_eq, leftBaire_pair, rightBaire_pair] using h

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Combine the recursive pair-tree normal form for analytic predicates with §{sec:edst-pair-tree-indices} to obtain
    a uniformly recursive sequence $\Sequence{T_e}{e\in\omega}$ representing every $\lSigma^1_1$ set by projection. The
    delayed
    finite-certificate construction supplies a total family of tree deciders without testing whether the original
    programs are total. Set
    $$
    V:=\{(e,p):\exists q\in\BaireSpace\ \forall n\;
      (\restrict{p}{n},\restrict{q}{n})\in T_e\}.
    $$
    This is $\lSigma^1_1$, and the pair-tree representation makes every $\lSigma^1_1$ set a section $V_e$. Now put
    $E:=\{p:(p(0),p)\notin V\}$. Its complement is the recursive preimage of $V$ under $p\mapsto(p(0),p)$, so $E$ is
    $\lPi^1_1$. If it were $\lSigma^1_1$, say $E=V_e$, then evaluating at a real $p$ with $p(0)=e$ would give $p\in E$ if
    and only if $p\notin E$. With a fixed oracle $a$, use the same recursive normal form relative to $a$; every step and the
    diagonal carry that oracle, so the proof relativizes verbatim.
-/
/-- The same universal family and diagonal proof work at every fixed oracle. -/
theorem effectiveAnalyticStrictness (ε : ℕ → ℕ) :
    ∃ E, Projected ε Eᶜ ∧ ¬ Projected ε E := by
  let V : ℕ → Set (ℕ → ℕ) := fun e => {p | (e,p) ∈ effectiveAnalyticUniversal ε}
  refine ⟨firstCoordinateDiagonal V, ?_, ?_⟩
  · convert effectiveAnalyticUniversal_diagonalPreimage ε using 1
    ext p
    simp [firstCoordinateDiagonal, V]
  · intro hE
    obtain ⟨e, he⟩ := effectiveAnalyticUniversal_universal ε _ hE
    exact firstCoordinateDiagonal_ne_section V e he

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{theorem*}[Effective analytic universal set and strictness]
-/
/-- The book's formula pointclass has the universal family and strictness at
zero and at every real parameter, via its proved pair-tree normal form. -/
theorem effectiveAnalyticUniversal_and_strictness (ε : ℕ → ℕ) :
    FormulaAnalytic ε {x | (leftBaire x 0, rightBaire x) ∈ effectiveAnalyticUniversal ε} ∧
    (∀ e, FormulaAnalytic ε {p | (e,p) ∈ effectiveAnalyticUniversal ε}) ∧
    (∀ A, FormulaAnalytic ε A → ∃ e, A = {p | (e,p) ∈ effectiveAnalyticUniversal ε}) ∧
    (∃ E, FormulaAnalytic ε Eᶜ ∧ ¬ FormulaAnalytic ε E) := by
  refine ⟨(effectiveAnalyticUniversal_projected ε).formulaAnalytic,
    fun e => (effectiveAnalyticUniversal_section ε e).formulaAnalytic,
    fun A hA => effectiveAnalyticUniversal_universal ε A hA.projected, ?_⟩
  obtain ⟨E, hE, hnot⟩ := effectiveAnalyticStrictness ε
  exact ⟨E, hE.formulaAnalytic, fun h => hnot h.projected⟩

end LambdaTree
end PolishSpaceBook
