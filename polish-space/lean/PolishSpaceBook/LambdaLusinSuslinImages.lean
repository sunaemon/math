module

public import PolishSpaceBook.LambdaUniformSetCodes
public import PolishSpaceBook.LambdaLusinSuslinGraphs

@[expose] public section

/-! # Uniform image and inverse-prefix indices from coherent prefix tests -/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance lusinImageListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance lusinImagePairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
variable {ε : ℕ → ℕ}

private theorem equal_decidable {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hF : NumericalComputes F f) (hG : NumericalComputes G g) :
    LambdaRelative.DecidablePredicate ε (fun i => f i = g i) := by
  apply numericalDecision (hF.combine hG equalityTerm_closed _ equalityTerm_apply) ε
  · intro i h; exact ite_eq_left h
  · intro i h; exact ite_eq_right h

/-- Input ((graph,word),competitor). -/
def earlierWord (z : ℕ) : Prop :=
  z.unpair.2 < z.unpair.1.unpair.2 ∧
    (NatListCode.decode z.unpair.2).length = (NatListCode.decode z.unpair.1.unpair.2).length

theorem earlierWord_decidable (ε : ℕ → ℕ) : LambdaRelative.DecidablePredicate ε earlierWord :=
  (numerical_lt_decidable (projection_computes false)
    (computes_codeSecond (projection_computes true)) ε).and
    (equal_decidable (listLength_computes.comp (projection_computes false))
      (listLength_computes.comp (computes_codeSecond (projection_computes true))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical transformations in these finite combinations are
    $$\begin{aligned}
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto
     \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
    \end{aligned}$$
    Pair projections, list length, list truncation, and numerical comparisons compute these transformations
    and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
    union use the empty set there. The parameter-preserving countable programs then implement both
    bounded operations. The finite-prefix lemma supplies both presentations of
    $$D_{e,s}:=\{y:(\restrict{y}{|s|},s)\in T_e\}.$$
    Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
    word code supplied as numerical data.
-/
def competitorCodeTerm := pairNumerical (codeFirst (numericalProjectionTerm true))
  (numericalProjectionTerm false)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical transformations in these finite combinations are
    $$\begin{aligned}
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto
     \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
    \end{aligned}$$
    Pair projections, list length, list truncation, and numerical comparisons compute these transformations
    and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
    union use the empty set there. The parameter-preserving countable programs then implement both
    bounded operations. The finite-prefix lemma supplies both presentations of
    $$D_{e,s}:=\{y:(\restrict{y}{|s|},s)\in T_e\}.$$
    Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
    word code supplied as numerical data.
-/
theorem competitorCode_computes : NumericalComputes competitorCodeTerm
    (fun z => Nat.pair z.unpair.1.unpair.1 z.unpair.2) :=
  (computes_codeFirst (projection_computes true)).pair (projection_computes false)

/-- Input ((graph,word),length); output (graph,restricted word). -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical transformations in these finite combinations are
    $$\begin{aligned}
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto
     \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
    \end{aligned}$$
    Pair projections, list length, list truncation, and numerical comparisons compute these transformations
    and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
    union use the empty set there. The parameter-preserving countable programs then implement both
    bounded operations. The finite-prefix lemma supplies both presentations of
    $$D_{e,s}:=\{y:(\restrict{y}{|s|},s)\in T_e\}.$$
    Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
    word code supplied as numerical data.
-/
def restrictedWordCodeTerm := pairNumerical (codeFirst (numericalProjectionTerm true))
  (numericalCompose listTakeTerm
    (pairNumerical (codeSecond (numericalProjectionTerm true)) (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical transformations in these finite combinations are
    $$\begin{aligned}
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto
     \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
    \end{aligned}$$
    Pair projections, list length, list truncation, and numerical comparisons compute these transformations
    and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
    union use the empty set there. The parameter-preserving countable programs then implement both
    bounded operations. The finite-prefix lemma supplies both presentations of
    $$D_{e,s}:=\{y:(\restrict{y}{|s|},s)\in T_e\}.$$
    Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
    word code supplied as numerical data.
-/
theorem restrictedWordCode_computes : NumericalComputes restrictedWordCodeTerm
    (fun z => Nat.pair z.unpair.1.unpair.1
      (NatListCode.encode ((NatListCode.decode z.unpair.1.unpair.2).take z.unpair.2))) := by
  simpa only [restrictedWordCodeTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
  (computes_codeFirst (projection_computes true)).pair
    (listTake_computes.comp ((computes_codeSecond (projection_computes true)).pair (projection_computes false)))

def withinWord (z : ℕ) : Prop := z.unpair.2 ≤ (NatListCode.decode z.unpair.1.unpair.2).length

theorem withinWord_decidable (ε : ℕ → ℕ) : LambdaRelative.DecidablePredicate ε withinWord :=
  numerical_le_decidable (projection_computes false)
    (listLength_computes.comp (computes_codeSecond (projection_computes true))) ε

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the image construction of §{sec:edst-effective-ls}, retain the graph index in every numerical
    input. Write $t_j$ for the unique finite word with code $j$. From the preceding separation indices set
    $$C_s:=\pi_0([T_{c(e,\LambdaListCode{s})}]),\qquad
    C'_s:=\pi_0([T_{d(e,\LambdaListCode{s})}]).$$
    Construct the first and coherent prefix tests, together with their negative counterparts, by
    $$\begin{aligned}
    B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j}},\\
    B_s^-&:=C'_s\cup\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j},\\
    H_s&:=\bigcap_{0\le k\le|s|}B_{\restrict{s}{k}},\\
    H_s^-&:=\bigcup_{0\le k\le|s|}B_{\restrict{s}{k}}^-.
    \end{aligned}$$
    The negative tests are complements of the corresponding positive tests whenever the separated
    input presentations are complementary. All families are nevertheless constructed on every numerical
    input. The index generator does not check that hypothesis.
-/
def firstPrefixPair (A : UniformSetPair ε) : UniformSetPair ε :=
  A.inter (((UniformSetPair.guard (earlierWord_decidable ε)).swap.union
    (A.reindex competitorCode_computes).swap).allNumbers)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the image construction of §{sec:edst-effective-ls}, retain the graph index in every numerical
    input. Write $t_j$ for the unique finite word with code $j$. From the preceding separation indices set
    $$C_s:=\pi_0([T_{c(e,\LambdaListCode{s})}]),\qquad
    C'_s:=\pi_0([T_{d(e,\LambdaListCode{s})}]).$$
    Construct the first and coherent prefix tests, together with their negative counterparts, by
    $$\begin{aligned}
    B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j}},\\
    B_s^-&:=C'_s\cup\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j},\\
    H_s&:=\bigcap_{0\le k\le|s|}B_{\restrict{s}{k}},\\
    H_s^-&:=\bigcup_{0\le k\le|s|}B_{\restrict{s}{k}}^-.
    \end{aligned}$$
    The negative tests are complements of the corresponding positive tests whenever the separated
    input presentations are complementary. All families are nevertheless constructed on every numerical
    input. The index generator does not check that hypothesis.
-/
def coherentPrefixPair (A : UniformSetPair ε) : UniformSetPair ε :=
  ((UniformSetPair.guard (withinWord_decidable ε)).swap.union
    ((firstPrefixPair A).reindex restrictedWordCode_computes)).allNumbers

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the image construction of §{sec:edst-effective-ls}, retain the graph index in every numerical
    input. Write $t_j$ for the unique finite word with code $j$. From the preceding separation indices set
    $$C_s:=\pi_0([T_{c(e,\LambdaListCode{s})}]),\qquad
    C'_s:=\pi_0([T_{d(e,\LambdaListCode{s})}]).$$
    Construct the first and coherent prefix tests, together with their negative counterparts, by
    $$\begin{aligned}
    B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j}},\\
    B_s^-&:=C'_s\cup\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j},\\
    H_s&:=\bigcap_{0\le k\le|s|}B_{\restrict{s}{k}},\\
    H_s^-&:=\bigcup_{0\le k\le|s|}B_{\restrict{s}{k}}^-.
    \end{aligned}$$
    The negative tests are complements of the corresponding positive tests whenever the separated
    input presentations are complementary. All families are nevertheless constructed on every numerical
    input. The index generator does not check that hypothesis.
-/
theorem correct_firstPrefixPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) (s : ℕ) :
    (firstPrefixPair A).CorrectAt (Nat.pair e s) := by
  apply (hA s).inter
  apply UniformSetPair.correct_allNumbers
  intro j
  apply (UniformSetPair.correct_guard _ _).swap.union
  apply UniformSetPair.CorrectAt.swap
  apply UniformSetPair.correct_reindex
  simpa only [Nat.unpair_pair] using hA j

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the image construction of §{sec:edst-effective-ls}, retain the graph index in every numerical
    input. Write $t_j$ for the unique finite word with code $j$. From the preceding separation indices set
    $$C_s:=\pi_0([T_{c(e,\LambdaListCode{s})}]),\qquad
    C'_s:=\pi_0([T_{d(e,\LambdaListCode{s})}]).$$
    Construct the first and coherent prefix tests, together with their negative counterparts, by
    $$\begin{aligned}
    B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j}},\\
    B_s^-&:=C'_s\cup\bigcup_{\substack{j<\LambdaListCode{s}\\|t_j|=|s|}}C_{t_j},\\
    H_s&:=\bigcap_{0\le k\le|s|}B_{\restrict{s}{k}},\\
    H_s^-&:=\bigcup_{0\le k\le|s|}B_{\restrict{s}{k}}^-.
    \end{aligned}$$
    The negative tests are complements of the corresponding positive tests whenever the separated
    input presentations are complementary. All families are nevertheless constructed on every numerical
    input. The index generator does not check that hypothesis.
-/
theorem correct_coherentPrefixPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) (s : ℕ) :
    (coherentPrefixPair A).CorrectAt (Nat.pair e s) := by
  apply UniformSetPair.correct_allNumbers
  intro n
  apply (UniformSetPair.correct_guard _ _).swap.union
  apply UniformSetPair.correct_reindex
  simpa only [Nat.unpair_pair] using correct_firstPrefixPair A hA
    (NatListCode.encode ((NatListCode.decode s).take n))

theorem mem_firstPrefixPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) (s : ℕ) (y : ℕ → ℕ) :
    y ∈ (firstPrefixPair A).positive (Nat.pair e s) ↔
      firstAcceptedPrefix (fun t => A.positive (Nat.pair e (NatListCode.encode t)))
        (NatListCode.decode s) y := by
  simp only [firstPrefixPair,UniformSetPair.inter,UniformSetPair.allNumbers,
    UniformSetPair.union,UniformSetPair.swap,UniformSetPair.reindex,mem_inter_iff,
    mem_iInter,mem_union,UniformSetPair.guard_negative,Nat.unpair_pair,earlierWord]
  simp only [UniformSetPair.CorrectAt] at hA
  simp only [hA,mem_compl_iff,firstAcceptedPrefix,NatListCode.encode_decode]
  constructor
  · rintro ⟨hs,h⟩
    exact ⟨hs,fun j hj hl => (h j).resolve_left (not_not.mpr ⟨hj,hl⟩)⟩
  · rintro ⟨hs,h⟩
    refine ⟨hs,fun j => ?_⟩
    by_cases hj : j < s ∧ (NatListCode.decode j).length = (NatListCode.decode s).length
    · exact Or.inr (h j hj.1 hj.2)
    · exact Or.inl hj

theorem mem_coherentPrefixPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) (s : ℕ) (y : ℕ → ℕ) :
    y ∈ (coherentPrefixPair A).positive (Nat.pair e s) ↔
      coherentPrefix (fun t => A.positive (Nat.pair e (NatListCode.encode t)))
        (NatListCode.decode s) y := by
  simp only [coherentPrefixPair,UniformSetPair.allNumbers,UniformSetPair.union,
    UniformSetPair.swap,UniformSetPair.reindex,mem_iInter,mem_union,
    UniformSetPair.guard_negative,Nat.unpair_pair,withinWord]
  simp only [mem_firstPrefixPair A hA,NatListCode.decode_encode,coherentPrefix]
  constructor
  · intro h n hn; exact (h n).resolve_left (not_not.mpr hn)
  · intro h n
    by_cases hn : n ≤ (NatListCode.decode s).length
    · exact Or.inr (h n hn)
    · exact Or.inl hn

/-- The output prefix and supplied word must form a node of the input graph tree. -/
theorem graphNode_decidable (ε : ℕ → ℕ) : LambdaRelative.DecidablePredicate ε
    (fun z : ℕ × List ℕ => (z.2,NatListCode.decode z.1.unpair.2) ∈ (indexedTree ε z.1.unpair.1).tree) := by
  exact (indexedTree_family_decidable ε).precompNumerical
    (g := fun z : ℕ × List ℕ => (z.1.unpair.1,(z.2,NatListCode.decode z.1.unpair.2)))
    ((computes_codeFirst (projection_computes true)).pair
      ((projection_computes false).pair (computes_codeSecond (projection_computes true))))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical transformations in these finite combinations are
    $$\begin{aligned}
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
    \NatPair{\NatPair{e}{j}}{k}&\longmapsto
     \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
    \end{aligned}$$
    Pair projections, list length, list truncation, and numerical comparisons compute these transformations
    and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
    union use the empty set there. The parameter-preserving countable programs then implement both
    bounded operations. The finite-prefix lemma supplies both presentations of
    $$D_{e,s}:=\{y:(\restrict{y}{|s|},s)\in T_e\}.$$
    Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
    word code supplied as numerical data.
-/
def graphNodePair (ε : ℕ → ℕ) : UniformSetPair ε :=
  UniformSetPair.prefixAtom (R := fun i s => (s,NatListCode.decode i.unpair.2) ∈ (indexedTree ε i.unpair.1).tree)
    (graphNode_decidable ε) (listLength_computes.comp (projection_computes false))

/-- Input ((graph,length),word). -/
def wordHasLength (z : ℕ) : Prop :=
  (NatListCode.decode z.unpair.2).length = z.unpair.1.unpair.2

theorem wordHasLength_decidable (ε : ℕ → ℕ) : LambdaRelative.DecidablePredicate ε wordHasLength :=
  equal_decidable (listLength_computes.comp (projection_computes false))
    (computes_codeSecond (projection_computes true))

def imageRowPair (A : UniformSetPair ε) : UniformSetPair ε :=
  (UniformSetPair.guard (wordHasLength_decidable ε)).inter
    (((coherentPrefixPair A).inter (graphNodePair ε)).reindex competitorCode_computes)

def imageFormulaPair (A : UniformSetPair ε) : UniformSetPair ε :=
  (imageRowPair A).someNumber.allNumbers

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Finally set
    $$\begin{aligned}
    R_{e,n,s}^+&:=\begin{cases}H_s\cap D_{e,s},&\Length{s}=n,\\\emptyset,&\Length{s}\ne n,\end{cases}\\
    R_{e,n,s}^-&:=\begin{cases}H_s^-\cup D_{e,s}^{\complement},&\Length{s}=n,\\\BaireSpace,&\Length{s}\ne n,\end{cases}\\
    A_e^+&:=\bigcap_{n\in\NN}\bigcup_{j\in\NN}R_{e,n,t_j}^+,\\
    A_e^-&:=\bigcup_{n\in\NN}\bigcap_{j\in\NN}R_{e,n,t_j}^-.
    \end{aligned}$$
    The length guard and both countable operations preserve joint finite-node decidability, including
    the outer graph index. The image formula gives the positive set, and complementarity of the input
    prefix tests gives the negative set. The inverse prefix sets and their negative presentations are
    $$A_e^+\cap C_s,\qquad A_e^-\cup C'_s.$$
    Specialize the four joint programs and substitute the graph index computed from the map and domain
    indices. This is the index construction used in the uniform effective Lusin--Suslin theorem.
-/
theorem correct_imageFormulaPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) : (imageFormulaPair A).CorrectAt e := by
  apply UniformSetPair.correct_allNumbers
  intro n
  apply UniformSetPair.correct_someNumber
  intro s
  apply (UniformSetPair.correct_guard _ _).inter
  apply UniformSetPair.correct_reindex
  simp only [Nat.unpair_pair]
  exact (correct_coherentPrefixPair A hA s).inter (by rfl)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Closed graph image by coherent prefix tests
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    If $\Pair{y}{x}\in[T_e]$, choose $s=\restrict{x}{n}$ at every length. The graph-prefix equivalence gives
    $y\in H_s$, and the branch condition gives membership of the finite pair.
    Conversely, choose a word $s_n$ at every length on the right-hand side. For $n\le m$, the word
    $\restrict{s_m}{n}$ has length $n$, and the output belongs to its coherent test. Disjointness at that
    length forces $s_n=\restrict{s_m}{n}$. These compatible words define a sequence $x$ with
    $\restrict{x}{n}=s_n$ for all $n$. Every finite pair belongs to the tree, so $\Pair{y}{x}\in[T_e]$.
    The argument includes the empty-graph case: satisfying the right-hand side would produce a branch.
-/
theorem mem_imageFormulaPair (A : UniformSetPair ε) {e : ℕ}
    (hA : ∀ s, A.CorrectAt (Nat.pair e s)) (y : ℕ → ℕ) :
    y ∈ (imageFormulaPair A).positive e ↔
      ∀ n, ∃ s : List ℕ, s.length = n ∧
        coherentPrefix (fun t => A.positive (Nat.pair e (NatListCode.encode t))) s y ∧
        (seqPrefix y n,s) ∈ (indexedTree ε e).tree := by
  simp only [imageFormulaPair,imageRowPair,UniformSetPair.allNumbers,UniformSetPair.someNumber,
    UniformSetPair.inter,UniformSetPair.reindex,mem_iInter,mem_iUnion,mem_inter_iff,
    UniformSetPair.guard_positive,Nat.unpair_pair,wordHasLength]
  simp only [mem_coherentPrefixPair A hA,graphNodePair,UniformSetPair.prefixAtom,mem_ofPred_eq,
    Nat.unpair_pair,Bool.false_eq_true,ite_false]
  constructor
  · intro h n
    obtain ⟨s,hl,hs,ht⟩ := h n
    exact ⟨NatListCode.decode s,hl,hs,by simpa only [hl] using ht⟩
  · intro h n
    obtain ⟨s,hl,hs,ht⟩ := h n
    refine ⟨NatListCode.encode s,?_,?_,?_⟩
    · simpa only [NatListCode.decode_encode] using hl
    · simpa only [NatListCode.decode_encode] using hs
    · simpa only [NatListCode.decode_encode,hl] using ht


def inverseFormulaPair (A : UniformSetPair ε) : UniformSetPair ε :=
  ((imageFormulaPair A).reindex (projection_computes true)).inter A

/-- No validity test is part of the four numerical generators. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Uniform effective Lusin--Suslin
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    First generate the graph index and its separated prefix tests. In the image formula, each finite
    condition that a prefix pair belongs to the graph tree is decidable from that prefix. It and its
    negation therefore have uniform tree presentations, by the finite-prefix construction of
    §{sec:lambda-lusin-image-programs}. Build the coherent tests and their negative counterparts together:
    complement exchanges the two presentations, intersection uses intersection on the positive side and
    union on the negative side, and union reverses these roles. Apply the parameter-preserving countable
    operations of §{sec:lambda-projection-programs} to the word codes and then to the
    lengths. The image identity proves that the positive presentation projects to the image; De Morgan's
    identities prove that the negative presentation projects to its complement. Intersect the image with
    each separated prefix test to obtain the inverse prefix sets, and take the union of the two negative
    presentations for their complements. Every stage retains the graph index and the relevant word and
    length codes as numerical inputs. Specialize the resulting fixed joint finite-node programs and compose
    with the graph-index generator. This gives all four total index maps without testing injectivity,
    nonemptiness, or termination of the supplied map program.
-/
theorem uniform_graph_image_inverse_indices (ε : ℕ → ℕ) :
    ∃ (M N I J : AlphaTerm) (m n i j : ℕ → ℕ),
      NumericalComputes M m ∧ NumericalComputes N n ∧
      NumericalComputes I i ∧ NumericalComputes J j ∧
      ∀ e, UniqueSections (indexedTree ε e).tree →
        indexedProjection ε (m e) = indexedProjection ε e ∧
        indexedProjection ε (n e) = (indexedProjection ε e)ᶜ ∧
        ∀ s, indexedProjection ε (i (Nat.pair e s)) =
          {y | ∃ x, (y,x) ∈ pairTreeBody (indexedTree ε e).tree ∧ x ∈ cyl (NatListCode.decode s)} ∧
          indexedProjection ε (j (Nat.pair e s)) =
          {y | ∃ x, (y,x) ∈ pairTreeBody (indexedTree ε e).tree ∧ x ∈ cyl (NatListCode.decode s)}ᶜ := by
  obtain ⟨C,D,c,d,hC,hD,hprefix⟩ := uniform_separated_prefix_indices ε
  let A : UniformSetPair ε :=
    ⟨fun z => indexedProjection ε (c z),fun z => indexedProjection ε (d z),
     ⟨fun z => indexedTree ε (c z),indexedTree_reindex_decidable ε hC,fun _ => rfl⟩,
     ⟨fun z => indexedTree ε (d z),indexedTree_reindex_decidable ε hD,fun _ => rfl⟩⟩
  obtain ⟨M,N,m,n,hM,hN,him⟩ := (imageFormulaPair A).indices
  obtain ⟨I,J,i,j,hI,hJ,hinv⟩ := (inverseFormulaPair A).indices
  refine ⟨M,N,I,J,m,n,i,j,hM,hN,hI,hJ,fun e hu => ?_⟩
  have hc (s) : A.CorrectAt (Nat.pair e s) := by
    simp only [UniformSetPair.CorrectAt,A,(hprefix e hu s).1,compl_compl]
  have hp (y x) (hx : (y,x) ∈ pairTreeBody (indexedTree ε e).tree) (s : List ℕ) :
      y ∈ A.positive (Nat.pair e (NatListCode.encode s)) ↔ x ∈ cyl s := by
    simpa only [A,NatListCode.decode_encode] using (hprefix e hu (NatListCode.encode s)).2 y x hx
  have he : (imageFormulaPair A).positive e = indexedProjection ε e := by
    ext y
    exact (mem_imageFormulaPair A hc y).trans
      (projection_iff_coherent_prefix_tests (indexedTree ε e).tree _ hp y).symm
  have hn := correct_imageFormulaPair A hc
  change (imageFormulaPair A).negative e = ((imageFormulaPair A).positive e)ᶜ at hn
  refine ⟨(him e).1.trans he,(him e).2.trans (hn.trans (congrArg (·ᶜ) he)),fun s => ?_⟩
  have heq : (inverseFormulaPair A).positive (Nat.pair e s) =
      {y | ∃ x, (y,x) ∈ pairTreeBody (indexedTree ε e).tree ∧ x ∈ cyl (NatListCode.decode s)} := by
    simp only [inverseFormulaPair,UniformSetPair.inter,UniformSetPair.reindex,
      Nat.unpair_pair,ite_true]
    rw [he]
    simpa only [NatListCode.encode_decode,indexedProjection] using
      (witness_prefix_projection_eq (indexedTree ε e).tree _ hp (NatListCode.decode s)).symm
  have hcomp : (inverseFormulaPair A).CorrectAt (Nat.pair e s) := by
    apply UniformSetPair.CorrectAt.inter
    · apply UniformSetPair.correct_reindex
      simpa only [Nat.unpair_pair,ite_true] using correct_imageFormulaPair A hc
    · exact hc s
  exact ⟨(hinv _).1.trans heq,(hinv _).2.trans (hcomp.trans (congrArg (·ᶜ) heq))⟩

/-- The complete compiler starts from the supplied map and closed-domain indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Uniform effective Lusin--Suslin
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A recursive injective continuous map $f:F\to\BaireSpace$ on a $\lPi^0_1$ closed set
    $F\IncludedIn\BaireSpace$ has $\lDelta^1_1$ image and a $\lDelta^1_1$ inverse. The uniform version
    requires image and inverse indices computed from the supplied map and domain indices.
    The closed-graph construction below isolates the prefix tests and image formula needed for this
    proof. In a pair-tree presentation of the graph, put the output in the first coordinate and its
    possible preimage in the second.
-/
theorem uniform_effective_lusin_suslin_indices (ε : ℕ → ℕ) :
    ∃ (M N I J : AlphaTerm) (m n i j : ℕ → ℕ),
      NumericalComputes M m ∧ NumericalComputes N n ∧
      NumericalComputes I i ∧ NumericalComputes J j ∧
      ∀ e p (T : Set (List ℕ)), LambdaRelative.Decides ε (Term.closedProgram p) (· ∈ T) →
      ∀ F : treeBody T → (ℕ → ℕ),
        (∀ x k, OracleRuns (pairBaire ε x.val) (Term.closedProgram e) k (F x k)) →
        Function.Injective F →
        indexedProjection ε (m (Nat.pair e p)) = Set.range F ∧
        indexedProjection ε (n (Nat.pair e p)) = (Set.range F)ᶜ ∧
        ∀ s, indexedProjection ε (i (Nat.pair (Nat.pair e p) s)) =
          {y | ∃ x, F x = y ∧ x.val ∈ cyl (NatListCode.decode s)} ∧
          indexedProjection ε (j (Nat.pair (Nat.pair e p) s)) =
          {y | ∃ x, F x = y ∧ x.val ∈ cyl (NatListCode.decode s)}ᶜ := by
  obtain ⟨G,g,hG,hg⟩ := uniform_closed_graph_indices ε
  obtain ⟨M,N,I,J,m,n,i,j,hM,hN,hI,hJ,hcodes⟩ := uniform_graph_image_inverse_indices ε
  have ht := (hG.comp (projection_computes true)).pair (projection_computes false)
  refine ⟨_,_,_,_,_,_,_,_,hM.comp hG,hN.comp hG,hI.comp ht,hJ.comp ht,
    fun e p T hT F hF hinj => ?_⟩
  have hgraph := hg e p T hT F hF
  have hu : UniqueSections (indexedTree ε (g (Nat.pair e p))).tree := by
    intro y x x' hx hx'
    obtain ⟨hx,hfx⟩ := (hgraph y x).mp hx
    obtain ⟨hx',hfx'⟩ := (hgraph y x').mp hx'
    exact congrArg Subtype.val (hinj (hfx.symm.trans hfx'))
  have hrange : indexedProjection ε (g (Nat.pair e p)) = Set.range F := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx,hy⟩ := (hgraph y x).mp hx
      exact ⟨⟨x,hx⟩,hy.symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,(hgraph (F x) x.val).mpr ⟨x.property,rfl⟩⟩
  obtain ⟨hm,hn,hi⟩ := hcodes (g (Nat.pair e p)) hu
  refine ⟨hm.trans hrange,hn.trans (congrArg (·ᶜ) hrange),fun s => ?_⟩
  simp only [Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false]
  have hs : {y | ∃ x, (y,x) ∈ pairTreeBody (indexedTree ε (g (Nat.pair e p))).tree ∧
      x ∈ cyl (NatListCode.decode s)} = {y | ∃ x, F x = y ∧ x.val ∈ cyl (NatListCode.decode s)} := by
    ext y
    constructor
    · rintro ⟨x,hx,hc⟩
      obtain ⟨hx,hy⟩ := (hgraph y x).mp hx
      exact ⟨⟨x,hx⟩,hy.symm,hc⟩
    · rintro ⟨x,rfl,hc⟩
      exact ⟨x.val,(hgraph (F x) x.val).mpr ⟨x.property,rfl⟩,hc⟩
  exact ⟨(hi s).1.trans hs,(hi s).2.trans (congrArg (·ᶜ) hs)⟩

end LambdaTree
end PolishSpaceBook
