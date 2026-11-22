module

public import PolishSpaceBook.LambdaNumericalSectionForest
public import PolishSpaceBook.LambdaEffectiveBoundedness
public import PolishSpaceBook.LambdaTransfiniteRankDecision

@[expose] public section

/-! # Complemented recursive projections are hyperarithmetic on the naturals

One Kleene--Brouwer order of the joint tree bounds all relevant sections.
Their numerical disjoint union has a single lambda edge decider. The uniform
rank evaluator decides its roots at one fixed stage and one fixed jump.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace LambdaTree
attribute [local instance] Classical.propDecidable

/-- The root position in the joint Kleene--Brouwer order bounds every section
on the first projection. The order and its root are independent of x. -/
theorem joint_order_bounds_sections {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    ∃ (W : WellOrderPresentation ε) (a : W.Carrier),
      ∀ x ∈ pairTreeProjection T.tree,
        RankBound.Holds W.order ((inferInstance : WellFounded W.order))
          (rootedSection S x).codedExtension a 0 := by
  let J := jointPrefixTree T S
  have hJ : WellFounded (strictTreeExtension J.tree) := jointTree_wellFounded T S hd
  let W := KleeneBrouwer.presentation J hJ
  have hroot : W.domain 0 := by
    change NatListCode.decode 0 ∈ (jointTree T S).tree
    simpa only [NatListCode.decode] using (jointTree T S).root_mem
  let a : W.Carrier := ⟨0,hroot⟩
  refine ⟨W,a,?_⟩
  rintro x ⟨p,hp⟩
  let f : ℕ → W.Carrier := fun c =>
    if hc : NatListCode.decode c ∈ (rootedSection S x).tree then
      ⟨NatListCode.encode (jointWord x p (NatListCode.decode c)),by
        change NatListCode.decode (NatListCode.encode _) ∈ (jointTree T S).tree
        rw [NatListCode.decode_encode]
        exact jointWord_mem T S x p hp _ hc⟩
    else a
  have hf : ∀ ⦃b c⦄, (rootedSection S x).codedExtension b c → W.order (f b) (f c) := by
    intro b c h
    change W.relation (f b).val (f c).val
    simp only [f,dite_eq_left h.1,dite_eq_left h.2.1]
    change KleeneBrouwer.Before
      (NatListCode.decode (NatListCode.encode (jointWord x p (NatListCode.decode b))))
      (NatListCode.decode (NatListCode.encode (jointWord x p (NatListCode.decode c))))
    simp only [NatListCode.decode_encode]
    exact KleeneBrouwer.extension_before (T := (jointTree T S).tree)
      (s := ⟨_,jointWord_mem T S x p hp _ h.1⟩)
      (t := ⟨_,jointWord_mem T S x p hp _ h.2.1⟩)
      ⟨jointWord_prefix x p h.2.2.1,by simpa only [jointWord_length] using h.2.2.2⟩
  have h := RankBound.holds_of_relation_preserving W.order ((inferInstance : WellFounded W.order))
    (rootedSection S x).codedExtension f hf 0
  have he : f 0 = a := by
    apply Subtype.ext
    simp only [f,NatListCode.decode]
    rw [dite_eq_left (rootedSection S x).root_mem]
    simp only [jointWord_nil,NatListCode.encode,a]
  rwa [he] at h

end LambdaTree
namespace KleeneNotation
open LambdaTree
attribute [local instance] Classical.propDecidable

/-- Numerical preimages use one fixed iterated jump and a concrete reindexing term. -/
theorem Hyperarithmetic.preimage {B : Set ℕ} (hB : Hyperarithmetic B)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) : Hyperarithmetic (f ⁻¹' B) := by
  obtain ⟨a,ha,P,hP⟩ := hB
  have h := hP.comp (ofNumerical hF (characteristic (iteratedJump ∅ a ha)))
  refine ⟨a,ha,_,h.1,?_⟩
  intro n
  simpa only [characteristic,mem_preimage] using h.2 n

/-- The reverse inclusion for subsets of N. No parameter or ordinal notation
is chosen separately for the numerical input. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For subsets of the natural numbers, §{sec:edst-hyperarithmetic-inclusion} proves
    $\HyperarithmeticalSets\IncludedIn\lDelta^1_1$. We prove the reverse inclusion with one fixed iterated
    jump for all numerical inputs. Let $B\IncludedIn\NN$ be $\lDelta^1_1$, and put
    $$A:=\{x\in\BaireSpace:x(0)\in B\}.$$
    Choose recursive pair trees $T,S$ whose projections are $A,A^{\complement}$. Form their rooted joint
    tree $J$ as in §{sec:edst-recursive-borel-completeness}. Its Kleene--Brouwer order has a recursive
    presentation $W=(D,R)$; let $a\in D$ be the code of its empty root.

    For $n\in\NN$, put $x_n(k)=n$ for every $k$ and let $S_n$ be the rooted section of $S$ at $x_n$.
    If $n\in B$, choose a witness $p$ with $(x_n,p)\in[T]$. The map
    $$t\longmapsto\WordPair{\restrict{x_n}{|t|}}{\WordPair{\restrict{p}{|t|}}{t}}$$
    sends $S_n$ into $J$ and preserves strict extension. Every strict extension precedes its prefix in the
    Kleene--Brouwer order, so this map proves that $S_n$ is well founded and its root rank is at most
    $\rho_W(a)$. The bound and its presentation do not depend on $n$ or on the chosen witness.
    If $n\notin B$, then $x_n\in A^{\complement}$, so $S_n$ has an infinite branch.

    Put all these sections into one numerical relation. If $u_j$ is the word with code $j$, define
    $$\begin{aligned}
     E(\NatPair{m}{j},\NatPair{n}{k})\quad\Longleftrightarrow\quad
     &m=n,\quad u_j,u_k\in S_n,\\
     &u_k\preceq u_j,\quad |u_k|<|u_j|.
    \end{aligned}$$
    §{sec:lambda-projection-programs} constructs a single total lambda decider for this
    relation. Its components do not interact. Coding a section therefore preserves well-foundedness below each node and
    all bounded-rank predicates, even when other sections have infinite branches. Consequently
    $$n\in B\quad\Longleftrightarrow\quad
     \NatPair{n}{0}\in Q_a,$$
    where $Q_a$ consists of those nodes below which $E$ is well founded and whose rank is at most $\rho_W(a)$.

    Apply the uniform rank-decision theorem in §{sec:edst-borel-rank-layers} to this fixed $W,E,a$ and
    starting set $\emptyset$. It gives one program $P_{d(a)}$ that decides $Q_a$ from
    $\chi_{(\IteratedJump{\emptyset}{g(a)})''}$. Precompose it with the closed numerical term
    $$N:=\lambdaab{n}{\LambdaNumericPair\,n\,\ChurchNumeral{0}}.$$
    The resulting program computes $\chi_B$. The input function is the characteristic function of the
    iterated jump at $\KleeneSuccIter{g(a)}{2}\in\KleeneO$, fixed independently of $n$. Thus
    $B\in\HyperarithmeticalSets$.
-/
theorem complemented_hyperarithmetic {B : Set ℕ}
    (hB : Complemented (fun _ => 0) {x | x 0 ∈ B}) : Hyperarithmetic B := by
  obtain ⟨⟨T,hT⟩,⟨S,hS⟩⟩ := hB
  have hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree) := by
    rw [← hT,← hS]
    exact disjoint_compl_right
  obtain ⟨W,a,ha⟩ := joint_order_bounds_sections T S hd
  have he (n : ℕ) : RankBound.StageHolds W (sectionForest S) a (Nat.pair n 0) ↔ n ∈ B := by
    change RankBound.Holds W.order _ (sectionForest S) a (Nat.pair n 0) ↔ _
    rw [show sectionForest S = (fun b c : ℕ => b.unpair.1 = c.unpair.1 ∧
      (rootedSection S (fun _ => c.unpair.1)).codedExtension b.unpair.2 c.unpair.2) from rfl,
      RankBound.holds_coded_family W.order ((inferInstance : WellFounded W.order))
        (fun n => (rootedSection S (fun _ => n)).codedExtension) a n 0]
    constructor
    · rintro ⟨hacc,_⟩
      by_contra hn
      have hx : (fun _ : ℕ => n) ∈ pairTreeProjection S.tree := by
        rw [← hS]; exact hn
      have hw := (rootedSection S (fun _ => n)).wellFounded_of_codedExtension
        ((rootedSection S (fun _ => n)).codedExtension_wellFounded_of_root_acc hacc)
      exact (prefixTreeWellFounded_iff _ (rootedSection S (fun _ => n)).downward).mpr hw
        ((branch_rootedSection_iff S (fun _ => n)).mpr hx)
    · intro hn
      apply ha (fun _ => n)
      rw [← hT]
      exact hn
  have hh := RankBound.rank_layer_hyperarithmetic W (sectionForest S) (sectionForest_decidable S) a
  have hp := hh.preimage (numericalIdentity_computes.pair (numericalConstant_computes 0))
  have heq : (fun n => Nat.pair n 0) ⁻¹' {s | RankBound.StageHolds W (sectionForest S) a s} = B := by
    ext n
    exact he n
  exact heq ▸ hp

theorem hyperarithmetic_iff_complemented (B : Set ℕ) :
    Hyperarithmetic B ↔ Complemented (fun _ => 0) {x | x 0 ∈ B} :=
  ⟨hyperarithmetic_complemented,complemented_hyperarithmetic⟩

/-- The arithmetic formula definition gives the same numerical characterization. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Kleene
  excerpt: |
    For subsets of $\omega$, one has $\lDelta^1_1=\HyperarithmeticalSets$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The hyperarithmetic and Borel hierarchies give parallel characterizations:
    $$
    \HyperarithmeticalSets \;=\; \lDelta^1_1,
    \qquad
    \bigcup_{1\le\alpha < \omegaOneOrd} \bSigma^0_\alpha \;=\; \bDelta^1_1.
    $$
-/
theorem hyperarithmetic_iff_formulaAnalytic (B : Set ℕ) :
    Hyperarithmetic B ↔ FormulaAnalytic (fun _ => 0) {x | x 0 ∈ B} ∧
      FormulaAnalytic (fun _ => 0) ({x | x 0 ∈ B}ᶜ) := by
  rw [formulaAnalytic_iff_projected,formulaAnalytic_iff_projected]
  exact hyperarithmetic_iff_complemented B

end KleeneNotation
end PolishSpaceBook
