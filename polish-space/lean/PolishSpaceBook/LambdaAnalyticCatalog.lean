module

public import PolishSpaceBook.LambdaIndexedTrees
public import PolishSpaceBook.ClosedPairTreeGeometry

@[expose] public section

/-! # Fixed-parameter analytic catalogs from lambda tree programs

The closed presentations use the total indexed family of delayed-rejection
trees. No test of program totality or projection nonemptiness is assumed.
This constructs the actual refinement hypotheses of witnessed fusion;
effective separation and the later kernel arguments are separate clients.
-/
namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance catalogListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance catalogPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

theorem projected_fusionCylinder (ε : ℕ → ℕ) {n : ℕ} (s : FusionPrefix n) :
    Projected ε (fusionCylinder s) := by
  rw [fusionCylinder_eq_cyl_ofFn]
  exact projected_cyl ε _

theorem projected_witnessProjection {ε : ℕ → ℕ} (T : PairTree ε)
    {n : ℕ} (s t : FusionPrefix n) :
    Projected ε (witnessProjection (pairTreeBody T.tree) s t) := by
  refine ⟨T.restrictPrefixes (List.ofFn s) (List.ofFn t), ?_⟩
  rw [pairTreeProjection_eq_image, pairTreeBody_restrictPrefixes]
  rw [← fusionCylinder_eq_cyl_ofFn, ← fusionCylinder_eq_cyl_ofFn]
  ext x
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    exact ⟨(x, y), ⟨hxy, hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hxy, hx, hy⟩, rfl⟩
    exact ⟨hx, y, hy, hxy⟩

/-- Every index gives a tree; valid deciders give every required projection.
The condition order consists of sets, so different indices may name one condition. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Closed presentations and refinements of the condition order
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the indexed trees from §{sec:edst-pair-tree-indices}. Every index gives a relative pair tree, and
    every relative pair-tree projection occurs among their projections. Their bodies are closed. There are
    only countably many indices, so there are only countably many represented sets, and hence only
    countably many nonempty ones. Different indices may represent the same condition; neither equality
    of the represented sets nor nonemptiness needs to be decidable.

    Restrict $T_e$ by requiring its point prefix to be comparable with $s$ and its witness prefix to be
    comparable with $t$. The prefix-restriction construction of §{sec:edst-relative-programs} has body
    $K_e\cap(\cyl{s}\times\cyl{t})$, so its projection is exactly $W_{e,s,t}$. Intersect its projection
    with $P$ by pairing witnesses. Cylinders themselves have relative pair-tree presentations, so the
    same intersection construction handles $P\cap\cyl{s}$. All component programs keep the original
    parameter. Nonemptiness is used only to regard the resulting set as a condition.
    \end{proof}
-/
def parameterAnalyticCatalog (ε : ℕ → ℕ) : AnalyticConditionCatalog where
  conditions := {P | Projected ε P.val}
  countable := (countable_projected ε).preimage Subtype.val_injective
  closed := fun i => pairTreeBody (indexedTree ε i).tree
  isClosed := fun i => isClosed_pairTreeBody _
  presentation := by
    intro P hP
    obtain ⟨i, hi⟩ := (projected_iff_index ε P.val).mp hP
    exact ⟨i, hi.trans (pairTreeProjection_eq_image _)⟩
  witness_refine := by
    intro P hP i n s t hne
    have hQ := hP.inter (projected_witnessProjection (indexedTree ε i) s t)
    exact ⟨⟨P.val ∩ witnessProjection (pairTreeBody (indexedTree ε i).tree) s t,
      hQ.analyticSet, hne⟩, hQ, Set.inter_subset_left, Set.inter_subset_right⟩
  cylinder_refine := by
    intro P hP n s hne
    have hQ := hP.inter (projected_fusionCylinder ε s)
    exact ⟨⟨P.val ∩ fusionCylinder s, hQ.analyticSet, hne⟩,
      hQ, Set.inter_subset_left, Set.inter_subset_right⟩

theorem mem_parameterAnalyticCatalog (ε : ℕ → ℕ) (P : AnalyticCondition FusionReal) :
    P ∈ (parameterAnalyticCatalog ε).conditions ↔ Projected ε P.val := Iff.rfl

theorem parameter_analytic_fusion (ε : ℕ → ℕ)
    (P : ℕ → (parameterAnalyticCatalog ε).Condition) (hP : Antitone P)
    (hmeet : ∀ D ∈ (parameterAnalyticCatalog ε).requirements, ∃ n, P n ∈ D) :
    ∃! x : FusionReal, ∀ n, x ∈ (P n).val.val :=
  (parameterAnalyticCatalog ε).fusion P hP hmeet

theorem parameter_requirements_countable_dense (ε : ℕ → ℕ) :
    (parameterAnalyticCatalog ε).requirements.Countable ∧
      ∀ D ∈ (parameterAnalyticCatalog ε).requirements, IsCoinitial D ∧ IsLowerSet D :=
  ⟨(parameterAnalyticCatalog ε).requirements_countable,
    (parameterAnalyticCatalog ε).requirements_dense_lower⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Generic points below a condition
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    We always include the
    witness tests just constructed when obtaining points by fusion. Countable families of additional tests are listed
    explicitly in the arguments that need them.
-/
theorem parameter_generic_point_below (ε : ℕ → ℕ)
    (A : (parameterAnalyticCatalog ε).Condition)
    (F : Set (Set (CatalogBelow (parameterAnalyticCatalog ε) A))) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) :
    ∃ x ∈ A.val.val, ∀ D ∈ F, ∃ Q ∈ D, x ∈ Q.val.val.val :=
  catalog_generic_point_below (parameterAnalyticCatalog ε) A F hFc hFd hFl

/-- Prescribed trees can be packed into one real, with a joint decider in
index and node. This is not a procedure for finding the parameter from sets. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Encode all node tests in one parameter by
    $$\varepsilon\bigl(\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}\bigr)
     =\begin{cases}1,&(s,t)\in T_i,\\0,&(s,t)\notin T_i.\end{cases}$$
    The list code and numerical pairing are bijective, so this specifies every coordinate without ambiguity.
    The closed lambda program that queries its parameter at its numerical input and returns the answer
    now decides the joint predicate. Fixing the first component gives a decider for each tree.
    This packs the required information into the parameter; it does not compute that parameter from an
    unspecified presentation of the analytic sets.
    \end{proof}
-/
theorem pairTrees_in_one_parameter (S : ℕ → Set (List ℕ × List ℕ))
    (hs : ∀ i z, z ∈ S i → z.1.length = z.2.length)
    (hd : ∀ i z, z ∈ S i → ∀ n, (z.1.take n, z.2.take n) ∈ S i) :
    ∃ ε : ℕ → ℕ, ∃ T : ℕ → PairTree ε,
      (∀ i, (T i).tree = S i) ∧
      LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree) := by
  classical
  let ε : ℕ → ℕ := fun z =>
    if (NatListCode.decode z.unpair.2.unpair.1, NatListCode.decode z.unpair.2.unpair.2) ∈ S z.unpair.1
    then 1 else 0
  have hr := numericalIdentity_computes.uniform.query
  have hj : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ S z.1) := by
    refine ⟨_,hr.1,fun z => ⟨?_,?_⟩⟩
    · intro hz
      simpa [ε,Encodable.encode,Encodable.encodeSigma,hz] using hr.2 ε (Encodable.encode z)
    · intro hz
      simpa [ε,Encodable.encode,Encodable.encodeSigma,hz] using hr.2 ε (Encodable.encode z)
  have hi (i : ℕ) : LambdaRelative.DecidablePredicate ε (fun z : List ℕ × List ℕ => z ∈ S i) := by
    exact hj.precompNumerical (g := fun z => (i,z))
      ((numericalConstant_computes i).pair numericalIdentity_computes)
      (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  exact ⟨ε,fun i => ⟨S i,hs i,hd i,hi i⟩,fun _ => rfl,hj⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: A common parameter for analytic presentations
-/
theorem analytic_family_in_one_parameter (A : ℕ → Set FusionReal)
    (hA : ∀ i, AnalyticSet (A i)) :
    ∃ ε : ℕ → ℕ, ∃ T : ℕ → PairTree ε,
      (∀ i, A i = pairTreeProjection (T i).tree) ∧
      LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree) := by
  choose K hK hKA using fun i => (analyticSet_iff_closed_baire_projection (A i)).mp (hA i)
  obtain ⟨ε, T, hT, hj⟩ := pairTrees_in_one_parameter (fun i => closedPairTreeCode (K i))
    (fun i => closedPairTreeCode_synchronized (K i))
    (fun i => closedPairTreeCode_downward (K i))
  refine ⟨ε,T,fun i => ?_,hj⟩
  rw [pairTreeProjection_eq_image, hT i, pairTreeBody_closedPairTreeCode _ (hK i), hKA i]

theorem analyticSet_iff_exists_parameter (A : Set FusionReal) :
    AnalyticSet A ↔ ∃ ε : ℕ → ℕ, Projected ε A := by
  constructor
  · intro hA
    obtain ⟨ε,T,hT,_⟩ := analytic_family_in_one_parameter (fun _ => A) (fun _ => hA)
    exact ⟨ε,T 0,hT 0⟩
  · rintro ⟨ε,hA⟩
    exact hA.analyticSet

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Thus any prescribed countable list of analytic data can be included before fixing the parameter.
    Once it is fixed, all later condition refinements must stay relative to it. Adding a further arbitrary
    analytic set later may require a different parameter and a different condition order.
-/
theorem analytic_conditions_in_one_catalog (P : ℕ → AnalyticCondition FusionReal) :
    ∃ ε : ℕ → ℕ, ∀ i, P i ∈ (parameterAnalyticCatalog ε).conditions := by
  obtain ⟨ε,T,hT,_⟩ := analytic_family_in_one_parameter (fun i => (P i).val)
    (fun i => (P i).property.1)
  exact ⟨ε,fun i => (mem_parameterAnalyticCatalog ε (P i)).mpr ⟨T i,hT i⟩⟩

end LambdaTree
end PolishSpaceBook
