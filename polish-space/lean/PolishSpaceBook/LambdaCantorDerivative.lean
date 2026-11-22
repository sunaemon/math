module

public import PolishSpaceBook.CantorDerivativeCoding
public import PolishSpaceBook.LambdaTreeMapPrograms
public import PolishSpaceBook.LambdaUniformDeciders

@[expose] public section

/-! # A four-jump lambda decider for a Cantor derivative tree

The matrix uses only decoded finite lists, bounded products, comparisons,
prefix tests and calls to the given tree decider. Two applications of the
universal-existential compiler implement its four numerical quantifiers.
-/
namespace PolishSpaceBook.CantorDerivative
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative LambdaTree
set_option maxHeartbeats 200000

private abbrev HasTerm (f : ℕ → ℕ) : Prop := ∃ P, NumericalComputes P f

private theorem HasTerm.comp {f g : ℕ → ℕ} (hf : HasTerm f) (hg : HasTerm g) :
    HasTerm (fun z => f (g z)) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨_, hF.comp hG⟩

private theorem HasTerm.pair {f g : ℕ → ℕ} (hf : HasTerm f) (hg : HasTerm g) :
    HasTerm (fun z => Nat.pair (f z) (g z)) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨_, hF.pair hG⟩

private theorem HasTerm.add {f g : ℕ → ℕ} (hf : HasTerm f) (hg : HasTerm g) :
    HasTerm (fun z => f z + g z) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨_, hF.add hG⟩

private theorem eq_uniform {ι : Type*} (ε : ι → ℕ → ℕ) {a b : ℕ → ℕ}
    (ha : HasTerm a) (hb : HasTerm b) :
    UniformlyDecidable ε (fun _ z => a z = b z) := by
  obtain ⟨A,hA⟩ := ha
  obtain ⟨B,hB⟩ := hb
  have h := (uniformly_decidable_le ε hA hB).and (uniformly_decidable_le ε hB hA)
  convert h using 1
  funext i z
  exact propext le_antisymm_iff

private theorem prefix_uniform {ι : Type*} (ε : ι → ℕ → ℕ) {a b : ℕ → ℕ}
    (ha : HasTerm a) (hb : HasTerm b) :
    UniformlyDecidable ε (fun _ z => NatListCode.decode (a z) <+: NatListCode.decode (b z)) := by
  obtain ⟨A,hA⟩ := ha
  obtain ⟨B,hB⟩ := hb
  exact uniformly_decidable_prefix ε hA hB

private theorem reindex_uniform {ι : Type*} {ε : ι → ℕ → ℕ} {R : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) {f : ℕ → ℕ} (hf : HasTerm f) :
    UniformlyDecidable ε (fun i z => R i (f z)) := by
  obtain ⟨F,hF⟩ := hf
  exact hR.reindex hF

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    First decide whether a word code is binary. In the first body decode $w=\NatPair{a}{i}$:
    $$\begin{aligned}
     G&:=\lambdaab{o}{\lambdaab{w}{L(a[i],\ChurchNumeral{1})}},\\
     B&:=\lambdaab{o}{\lambdaab{a}{\LambdaRelativeProduct{G}\,o\,
      (\LambdaNumericPair\,a\,\ell(a))}}.
    \end{aligned}$$
    The product tests every entry, so $B$ returns one exactly for words with entries zero or one.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ decide membership in the input tree at $\varepsilon$, using the natural-list code for a
    binary word. Extend the test to natural words by rejecting nonbinary words. Write
    $$\begin{aligned}
     \ell(a)&:=\LambdaListLength\,a,\qquad a[i]:=\LambdaListGet(\LambdaNumericPair\,a\,i),\\
     E(a,b)&:=\LambdaEqual\,a\,b,\qquad
     F(a,b):=\LambdaListPrefix(\LambdaNumericPair\,a\,b),\\
     L(a,b)&:=\LambdaLeCase{a}{b}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
     Z&:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    All products below mean repeated application of $\LambdaMul$. Expand every abbreviation before
    abstraction, use numerical projections to decode paired inputs, and choose distinct fresh binders.
-/
theorem binary_uniform {ι : Type*} (ε : ι → ℕ → ℕ) :
    UniformlyDecidable ε (fun _ => Binary) := by
  have h := (uniformly_decidable_le ε listGet_computes (numericalConstant_computes 1)).boundedAll
    listLength_computes
  have he : (fun z : ℕ => ∀ i < (NatListCode.decode z).length,
      (NatListCode.decode z).getD i 0 ≤ 1) = Binary := by
    funext z
    apply propext
    constructor
    · intro hi a ha
      obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp ha
      simpa [List.getD, hi'] using hi i hi'
    · intro ha i hi
      apply ha
      simp [List.getD, hi]
  simpa only [Nat.unpair_pair, ← he] using h

theorem binary_decidable (ε : ℕ → ℕ) : DecidablePredicate ε Binary := by
  obtain ⟨P,_,hP⟩ := binary_uniform (fun _ : Unit => ε)
  exact ⟨P,hP ()⟩

abbrev matrixWord (z : ℕ) := z.unpair.1.unpair.1.unpair.1.unpair.1
abbrev matrixCount (z : ℕ) := z.unpair.1.unpair.1.unpair.1.unpair.2
abbrev matrixChoice (z : ℕ) := z.unpair.1.unpair.1.unpair.2
abbrev matrixLevel (z : ℕ) := z.unpair.1.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Decode the matrix input as
    $$z=\NatPair{\NatPair{\NatPair{\NatPair{s}{m}}{c}}{n}}{V},\qquad c=\NatPair{N}{U}.$$
    Here $s$ is a word code and $U,V$ are table codes. Put $u_i:=U[i]$, $v_i:=V[i]$, and use
    $$\begin{aligned}
     A(o,z,i):={}&(Bo u_i)(Bo v_i)E(\ell(u_i),N)F(s,u_i)\\
     &\cdot E(\ell(v_i),\LambdaAdd\,N\,n)F(u_i,v_i)(Po v_i),\\
     C(z,i,j):={}&Z\bigl(\LambdaMul\,E(u_i,u_j)\,(Z(E(i,j)))\bigr).
    \end{aligned}$$
    The first body checks one row of $R_T$. The second checks that equality of the two word codes
    implies equality of their indices. Injectivity of list coding identifies equality of codes with
    equality of words.
-/
def matrix (T : Set (List ℕ)) (z : ℕ) : Prop :=
  NumericTest T (matrixWord z) (matrixCount z) (matrixChoice z) (matrixLevel z) z.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    List access and every numerical comparison terminate. Each call of $B$ is a bounded product of
    comparison bits, and each tree test is one call of $P$ on the extracted word code. Hence $A_P$
    returns exactly the bit for its row. The inner product in $C_1$ checks every $j<m$ for the fixed
    $i$; its outer product checks every $i<m$. These are exactly the distinctness conditions.
    Multiplying by the binary test for $s$ and by all row bits gives precisely $R_T$. The bounded-product
    reductions keep the same input function in every call. At bound zero they return one, and missing
    table entries return the empty-word code, as stipulated in the definition.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite derivative-test program
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Decode the matrix input as
    $$z=\NatPair{\NatPair{\NatPair{\NatPair{s}{m}}{c}}{n}}{V},\qquad c=\NatPair{N}{U}.$$
    Here $s$ is a word code and $U,V$ are table codes. Put $u_i:=U[i]$, $v_i:=V[i]$, and use
    $$\begin{aligned}
     A(o,z,i):={}&(Bo u_i)(Bo v_i)E(\ell(u_i),N)F(s,u_i)\\
     &\cdot E(\ell(v_i),\LambdaAdd\,N\,n)F(u_i,v_i)(Po v_i),\\
     C(z,i,j):={}&Z\bigl(\LambdaMul\,E(u_i,u_j)\,(Z(E(i,j)))\bigr).
    \end{aligned}$$
    The first body checks one row of $R_T$. The second checks that equality of the two word codes
    implies equality of their indices. Injectivity of list coding identifies equality of codes with
    equality of words.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Form $A_P:=\lambdaab{o}{\lambdaab{w}{A(o,z,i)}}$ with $w=\NatPair{z}{i}$, and
    $C_0:=\lambdaab{o}{\lambdaab{w}{C(z,i,j)}}$ with $w=\NatPair{\NatPair{z}{i}}{j}$.
    For $w=\NatPair{z}{i}$ define
    $$C_1:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{C_0}\,o\,
     (\LambdaNumericPair\,w\,m)}}.$$
    Finally define
    $$\begin{aligned}
     M_P:=\lambdaab{o}{\lambdaab{z}{(Bo s)
     &\cdot\bigl(\LambdaRelativeProduct{A_P}\,o\,(\LambdaNumericPair\,z\,m)\bigr)\\
     &\cdot\bigl(\LambdaRelativeProduct{C_1}\,o\,(\LambdaNumericPair\,z\,m)\bigr)}}.
    \end{aligned}$$
    In each body, $m$ is extracted from its retained input $z$.
-/
theorem matrix_uniform_family {ι : Type*} (ε : ι → ℕ → ℕ) (T : ι → Set (List ℕ))
    (hT : UniformlyDecidable ε (fun i (e : ℕ) => NatListCode.decode e ∈ T i)) :
    UniformlyDecidable ε (fun i => matrix (T i)) := by
  have hp : HasTerm (fun z : ℕ => z.unpair.1) := ⟨_, projection_computes true⟩
  have hq : HasTerm (fun z : ℕ => z.unpair.2) := ⟨_, projection_computes false⟩
  have hlen : HasTerm (fun z : ℕ => (NatListCode.decode z).length) := ⟨_, listLength_computes⟩
  have hget : HasTerm (fun z : ℕ => tableAt z.unpair.1 z.unpair.2) := ⟨_, listGet_computes⟩
  have hpp := hp.comp hp
  have hppp := hp.comp hpp
  have hs := hp.comp hppp
  have hm := hq.comp hppp
  have hc := hq.comp hpp
  have hn := hq.comp hp
  have hN := hp.comp hc
  have hU := hq.comp hc
  have hbin := binary_uniform ε
  have hbins := reindex_uniform hbin hs
  have hui := hget.comp ((hU.comp hp).pair hq)
  have hvi := hget.comp ((hq.comp hp).pair hq)
  have hbui := reindex_uniform hbin hui
  have hbvi := reindex_uniform hbin hvi
  have hlu := eq_uniform ε (hlen.comp hui) (hN.comp hp)
  have hsu := prefix_uniform ε (hs.comp hp) hui
  have hlv := eq_uniform ε (hlen.comp hvi) ((hN.add hn).comp hp)
  have huv := prefix_uniform ε hui hvi
  have hvt := reindex_uniform hT hvi
  obtain ⟨M, hM⟩ := hm
  have hrows := (hbui.and (hbvi.and (hlu.and (hsu.and (hlv.and (huv.and hvt)))))).boundedAll hM
  have hleft := hget.comp ((hU.comp hpp).pair (hq.comp hp))
  have hright := hget.comp ((hU.comp hpp).pair hq)
  have hdistinct := ((eq_uniform ε hleft hright).imp (eq_uniform ε (hq.comp hp) hq)).boundedAll
    (hM.comp (projection_computes true))
  have hdistinct' := hdistinct.boundedAll hM
  convert hbins.and (hrows.and hdistinct') using 1
  funext i z
  simp only [matrix, NumericTest, matrixWord, matrixCount, matrixChoice, matrixLevel,
    tableAt, Nat.unpair_pair, ite_true]

/-- The finite derivative test is selected before the parameter and the input tree. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The construction is uniform in both the parameter and the tree. Fix the closed term $P$ first.
    All selectors and numerical comparisons above are independent of the parameter. Boolean operations
    combine the supplied decision bits, reindexing changes only their numerical arguments, and bounded
    products repeat the same closed body with the same input function. Thus one term $M_P$ works for
    every $\varepsilon$ and every $T$ whose membership is decided by $P$ at $\varepsilon$.
    This is stronger than choosing a separate matrix program after each parameter has been fixed.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite derivative-test program
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Form $A_P:=\lambdaab{o}{\lambdaab{w}{A(o,z,i)}}$ with $w=\NatPair{z}{i}$, and
    $C_0:=\lambdaab{o}{\lambdaab{w}{C(z,i,j)}}$ with $w=\NatPair{\NatPair{z}{i}}{j}$.
    For $w=\NatPair{z}{i}$ define
    $$C_1:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{C_0}\,o\,
     (\LambdaNumericPair\,w\,m)}}.$$
    Finally define
    $$\begin{aligned}
     M_P:=\lambdaab{o}{\lambdaab{z}{(Bo s)
     &\cdot\bigl(\LambdaRelativeProduct{A_P}\,o\,(\LambdaNumericPair\,z\,m)\bigr)\\
     &\cdot\bigl(\LambdaRelativeProduct{C_1}\,o\,(\LambdaNumericPair\,z\,m)\bigr)}}.
    \end{aligned}$$
    In each body, $m$ is extracted from its retained input $z$.
-/
theorem matrix_program (P : AlphaTerm) (hP : P.Closed) :
    ∃ M : AlphaTerm, M.Closed ∧ ∀ (ε : ℕ → ℕ) (T : Set (List ℕ)),
      Decides ε P (fun e : ℕ => NatListCode.decode e ∈ T) → Decides ε M (matrix T) := by
  let I := {q : (ℕ → ℕ) × Set (List ℕ) //
    Decides q.1 P (fun e : ℕ => NatListCode.decode e ∈ q.2)}
  have h := matrix_uniform_family (fun i : I => i.val.1) (fun i : I => i.val.2)
    ⟨P,hP,fun i => i.property⟩
  obtain ⟨M,hM,h⟩ := h
  exact ⟨M,hM,fun ε T hd => h ⟨(ε,T),hd⟩⟩

theorem matrix_decidable {ε : ℕ → ℕ} {T : Set (List ℕ)}
    (hT : DecidablePredicate ε (fun e : ℕ => NatListCode.decode e ∈ T)) :
    DecidablePredicate ε (matrix T) := by
  obtain ⟨P,hP⟩ := hT
  obtain ⟨M,_,hM⟩ := matrix_program P hP.1
  exact ⟨M,hM ε T hP⟩

noncomputable abbrev fourthJump (ε : ℕ → ℕ) := jumpName (jumpName (jumpName (jumpName ε)))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The matrix $R_T$ is a finite test using list access, lengths, comparisons, prefix tests, and calls
    to the decider for $T$. §{sec:lambda-cantor-derivative-programs} gives its closed lambda
    construction. Apply the numerical-quantifier compiler of §{sec:lambda-relative-jump} to the
    innermost existential quantifier, then the universal one, and repeat. These four steps give the
    claimed membership decider. Empty tables cause no exception: their bounded products return one.
-/
/-- The same four-jump term works for every parameter and every tree decided by `P`. -/
theorem derivative_test_program (P : AlphaTerm) (hP : P.Closed) :
    ∃ D : AlphaTerm, D.Closed ∧ ∀ (ε : ℕ → ℕ) (T : Set (List ℕ)),
      Decides ε P (fun e : ℕ => NatListCode.decode e ∈ T) →
      Decides (fourthJump ε) D (fun s : ℕ => ∀ m, ∃ c, ∀ n, ∃ V, NumericTest T s m c n V) := by
  obtain ⟨M,hM,hm⟩ := matrix_program P hP
  obtain ⟨Q,hQ,hinner⟩ := exists_forall_exists_jump_program M hM
  obtain ⟨D,hD,houter⟩ := exists_forall_exists_jump_program Q hQ
  refine ⟨D,hD,fun ε T hd => ?_⟩
  have hi := hinner ε
    (fun a n V => NumericTest T a.unpair.1.unpair.1 a.unpair.1.unpair.2 a.unpair.2 n V)
    (hm ε T hd)
  exact houter (jumpName (jumpName ε)) (fun s m c => ∀ n, ∃ V, NumericTest T s m c n V) hi

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Uniformity of the derivative program
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The finite matrix program in §{sec:lambda-cantor-derivative-programs} is built from the fixed
    program $P$ by numerical reindexing, Boolean operations, and bounded products. Its syntax uses
    neither $T$ nor $\varepsilon$. The four numerical-quantifier transformations also depend only on
    the program being transformed. Their composition therefore gives one $Q$ that works for every
    parameter and tree satisfying the hypothesis. The preceding proposition identifies its decided
    predicate with membership in the derivative tree, including when the original tree is empty.
    \end{proof}
-/
theorem derivative_program_uniform (P : AlphaTerm) (hP : P.Closed) :
    ∃ D : AlphaTerm, D.Closed ∧ ∀ (ε : ℕ → ℕ) (T : Set (List ℕ)), IsSubtree T →
      Decides ε P (fun e : ℕ => NatListCode.decode e ∈ T) → ∀ s : List Bool,
      (s ∈ derivativeTree (binaryTree T) → OracleRuns (fourthJump ε) D (encodeWord s) 1) ∧
      (s ∉ derivativeTree (binaryTree T) → OracleRuns (fourthJump ε) D (encodeWord s) 0) := by
  obtain ⟨D,hD,hd⟩ := derivative_test_program P hP
  refine ⟨D,hD,fun ε T hsub ht s => ?_⟩
  have h := hd ε T ht
  exact ⟨fun hs => (h.2 _).1 ((derivative_numeric_iff hsub s).mp hs),
    fun hs => (h.2 _).2 (fun h => hs ((derivative_numeric_iff hsub s).mpr h))⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    If $e$ is an index of $M_P$, apply the index transformations in §{sec:lambda-relative-jump}:
    $$\upsilon(\xi(\upsilon(\xi(e)))).$$
    The first pair removes $V,n$, and the second removes $c,m$. The resulting program uses four
    successive jumps and decides the derivative-tree predicate proved in §{sec:edst-effective-cb}.
-/
theorem derivative_test_decidable {ε : ℕ → ℕ} {T : Set (List ℕ)}
    (hT : DecidablePredicate ε (fun e : ℕ => NatListCode.decode e ∈ T)) :
    DecidablePredicate (fourthJump ε) (fun s : ℕ => ∀ m, ∃ c, ∀ n, ∃ V, NumericTest T s m c n V) := by
  obtain ⟨P, hP⟩ := matrix_decidable hT
  obtain ⟨Q, hQ, hquant⟩ := exists_forall_exists_jump_program P hP.1
  have hinner := hquant ε
    (fun a n V => NumericTest T a.unpair.1.unpair.1 a.unpair.1.unpair.2 a.unpair.2 n V) hP
  obtain ⟨R, _, houter⟩ := exists_forall_exists_jump_program Q hQ
  exact ⟨R, houter (jumpName (jumpName ε))
    (fun s m c => ∀ n, ∃ V, NumericTest T s m c n V) hinner⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: One effective derivative step
-/
theorem derivative_program {ε : ℕ → ℕ} {T : Set (List ℕ)} (hsub : IsSubtree T)
    (hT : DecidablePredicate ε (fun e : ℕ => NatListCode.decode e ∈ T)) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ s : List Bool,
      (s ∈ derivativeTree (binaryTree T) → OracleRuns (fourthJump ε) P (encodeWord s) 1) ∧
      (s ∉ derivativeTree (binaryTree T) → OracleRuns (fourthJump ε) P (encodeWord s) 0) := by
  obtain ⟨P, hP⟩ := derivative_test_decidable hT
  exact ⟨P, hP.1, fun s => ⟨fun hs => (hP.2 _).1 ((derivative_numeric_iff hsub s).mp hs),
    fun hs => (hP.2 _).2 (fun h => hs ((derivative_numeric_iff hsub s).mpr h))⟩⟩

end PolishSpaceBook.CantorDerivative
