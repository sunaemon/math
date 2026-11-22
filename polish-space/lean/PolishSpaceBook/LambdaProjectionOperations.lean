module

public import PolishSpaceBook.LambdaFiniteCheckTrees
public import PolishSpaceBook.LambdaListTabulation
public import PolishSpaceBook.BairePairGeometry

@[expose] public section

/-! # Existential coordinate projection and relational images

The omitted coordinate and the old witness are coded together entrywise.
All finite tests use actual lambda programs at the original fixed parameter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance projectionListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance projectionPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Input ((first-word,second-word),position) returns the paired entries. -/
def pairWordEntryTerm : AlphaTerm :=
  pairNumerical
    (numericalCompose listGetTerm
      (pairNumerical (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
        (numericalProjectionTerm false)))
    (numericalCompose listGetTerm
      (pairNumerical (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
        (numericalProjectionTerm false)))

theorem pairWordEntry_computes : NumericalComputes pairWordEntryTerm (fun z => Nat.pair
    ((NatListCode.decode z.unpair.1.unpair.1).getD z.unpair.2 0)
    ((NatListCode.decode z.unpair.1.unpair.2).getD z.unpair.2 0)) := by
  simpa [pairWordEntryTerm] using
    (listGet_computes.comp (((projection_computes true).comp (projection_computes true)).pair
      (projection_computes false))).pair
    (listGet_computes.comp (((projection_computes false).comp (projection_computes true)).pair
      (projection_computes false)))

def pairWordsTerm : AlphaTerm := numericalCompose (listTabulateTerm pairWordEntryTerm)
  (pairNumerical numericalIdentity (numericalCompose listLengthTerm (numericalProjectionTerm true)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For paired words, decode $v=\NatPair{w}{k}$ inside the following term bodies:
    $$\begin{aligned}
    F_{\mathrm{pair}}&:=\lambdaab{v}{\LambdaNumericPair\,
     (\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,k))\,
     (\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,k))},\\
    \LambdaListPair&:=\lambdaab{z}{\LambdaListTabulate{F_{\mathrm{pair}}}\,
     (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{1}z)))}.
    \end{aligned}$$
    Expand $w,k$ inside the body of $F_{\mathrm{pair}}$ before abstraction. On the code of $(s,t)$,
    this returns $\LambdaListCode{\WordPair{s}{t}}$: the list has length $|s|$, and its $k$th entry pairs the
    $k$th entries of the two words, with zero used beyond the length of $t$. The finite-tabulation lemma and
    the total list-access theorem prove this even when the input lengths differ.
-/
theorem pairWords_computes : NumericalComputes pairWordsTerm (fun z =>
    NatListCode.encode (pairWords (NatListCode.decode z.unpair.1) (NatListCode.decode z.unpair.2))) := by
  simpa only [pairWordsTerm,pairWords,Nat.unpair_pair,id_eq,ite_true] using
    (listTabulate_computes pairWordEntry_computes).comp
      (numericalIdentity_computes.pair (listLength_computes.comp (projection_computes true)))

def rightProjectionInputTerm : AlphaTerm := pairNumerical
  (numericalCompose pairWordsTerm
    (pairNumerical (numericalCompose (witnessProjectionTerm true) (numericalProjectionTerm false))
      (numericalProjectionTerm true)))
  (numericalCompose (witnessProjectionTerm false) (numericalProjectionTerm false))

theorem rightProjectionInput_computes : NumericalComputes rightProjectionInputTerm (fun z =>
    Nat.pair
      (NatListCode.encode (pairWords (leftWitness (NatListCode.decode z.unpair.2)) (NatListCode.decode z.unpair.1)))
      (NatListCode.encode (rightWitness (NatListCode.decode z.unpair.2)))) := by
  simpa only [rightProjectionInputTerm,leftWitness,rightWitness,Nat.unpair_pair,NatListCode.decode_encode,
    ite_true,Bool.false_eq_true,ite_false] using
    (pairWords_computes.comp (((witnessProjection_computes true).comp (projection_computes false)).pair
      (projection_computes true))).pair
    ((witnessProjection_computes false).comp (projection_computes false))

def rightProjectionTest (T : Set (List ℕ × List ℕ)) (z : List ℕ × List ℕ) : Prop :=
  (pairWords (leftWitness z.2) z.1,rightWitness z.2) ∈ T

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Suppose $P$ decides membership in a pair tree $T$ relative to a fixed parameter. Set
    $A_i:=\LambdaListMap\,\LambdaNumericProjection{i}$ for $i=1,2$. For the code $z=\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}$, abbreviate
    $v(z)=\LambdaNumericProjection{2}z$, and define
    $$\begin{aligned}
    K&:=\lambdaab{z}{\LambdaNumericPair\,
     \bigl(\LambdaListPair(\LambdaNumericPair\,(A_1v(z))\,(\LambdaNumericProjection{1}z))\bigr)\,(A_2v(z))},\\
    Q&:=\lambdaab{o}{\lambdaab{z}{Po(Kz)}}.
    \end{aligned}$$
    The program $Q$ decides the test $(\WordPair{t_1}{s},t_2)\in T$, where $t_1,t_2$ are the entrywise
    projections of $t$. Indeed, list mapping supplies these two projections, $\LambdaListPair$ pairs the
    first with $s$, and numerical pairing supplies the exact input for $P$. Each component terminates and
    the input parameter is unchanged. Applying the finite-test construction of
    §{sec:lambda-kleene-brouwer} to $Q$ gives the projection-tree decider of
    §{sec:edst-coordinate-projections}. At the empty node it tests the empty pair in $T$, so it also handles
    an empty original tree correctly.
-/
theorem rightProjectionTest_decidable {ε : ℕ → ℕ} (T : PairTree ε) :
    LambdaRelative.DecidablePredicate ε (rightProjectionTest T.tree) :=
  T.decidable.precompNumerical (g := fun z : List ℕ × List ℕ =>
    (pairWords (leftWitness z.2) z.1,rightWitness z.2)) rightProjectionInput_computes
    (fun z => by simp [Encodable.encode])

/-- The new witness contains the omitted point and the old witness. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Coordinate projection of a relative tree
-/
def PairTree.projectRight {ε : ℕ → ℕ} (T : PairTree ε) : PairTree ε :=
  finiteCheckTree (rightProjectionTest T.tree) (rightProjectionTest_decidable T)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For a finite word $v$, write $v_1,v_2$ for its entrywise projections. Use the finite test
    $$R(s,v)\quad\Longleftrightarrow\quad(\WordPair{v_1}{s},v_2)\in T.$$
    List mapping computes $v_1,v_2$; the finite-tabulation program in §{sec:lambda-projection-programs}
    computes the paired word. Hence this test is decidable relative to $\varepsilon$. Apply the finite-test
    construction of §{sec:edst-finite-check-trees} to obtain $S$, including the test at length zero.
    Its body consists exactly of the pairs satisfying every prefix test. Commutation with prefixes gives
    the displayed body identity.
-/
theorem pairTreeBody_projectRight {ε : ℕ → ℕ} (T : PairTree ε) (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody T.projectRight.tree ↔
      (pairBaire (leftBaire q) x,rightBaire q) ∈ pairTreeBody T.tree := by
  change (x,q) ∈ pairTreeBody (finiteCheckNodes (rightProjectionTest T.tree)) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  simp only [Set.mem_ofPred_eq,rightProjectionTest,leftWitness_prefix,rightWitness_prefix,
    pairWords_prefix,pairTreeBody]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    A witness $u$ for $x\in\pi_0([S])$ gives the point $\NamePair{\NameProjection{1}{u}}{x}$ in
    $\pi_0([T])$, with witness $\NameProjection{2}{u}$. Conversely, if $(p,q)\in[T]$, use
    $u=\NamePair{\NameProjection{1}{p}}{q}$ as the witness for $\NameProjection{2}{p}$ in the new tree.
    The inverse identities for pairing prove both assertions. To omit the other coordinate, first swap the
    two point coordinates. The swap is computed entrywise by the numerical projections and pairing, so
    §{sec:edst-finite-check-trees} supplies its inverse image before applying the construction just proved.
    No new parameter and no decision procedure for the projected set are required.
    \end{proof}
-/
theorem pairTreeProjection_projectRight {ε : ℕ → ℕ} (T : PairTree ε) :
    pairTreeProjection T.projectRight.tree = rightBaire '' pairTreeProjection T.tree := by
  ext x
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨pairBaire (leftBaire q) x,⟨rightBaire q,(pairTreeBody_projectRight T x q).mp hq⟩,
      rightBaire_pair _ _⟩
  · rintro ⟨p,⟨q,hq⟩,rfl⟩
    refine ⟨pairBaire (leftBaire p) q,(pairTreeBody_projectRight T _ _).mpr ?_⟩
    simpa only [leftBaire_pair,rightBaire_pair,pairBaire_left_right] using hq

theorem Projected.projectRight {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : Projected ε (rightBaire '' A) := by
  obtain ⟨T,rfl⟩ := hA
  exact ⟨T.projectRight,(pairTreeProjection_projectRight T).symm⟩

theorem Projected.leftPreimage {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : Projected ε (leftBaire ⁻¹' A) :=
  hA.coordinatePreimage (projection_computes true)

theorem Projected.rightPreimage {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : Projected ε (rightBaire ⁻¹' A) :=
  hA.coordinatePreimage (projection_computes false)

theorem Projected.projectLeft {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : Projected ε (leftBaire '' A) := by
  have hs : Projected ε {p | pairBaire (rightBaire p) (leftBaire p) ∈ A} :=
    hA.coordinatePreimage ((projection_computes false).pair (projection_computes true))
  have hi := hs.projectRight
  have heq : rightBaire '' {p | pairBaire (rightBaire p) (leftBaire p) ∈ A} = leftBaire '' A := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨pairBaire (rightBaire p) (leftBaire p),hp,leftBaire_pair _ _⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨pairBaire (rightBaire p) (leftBaire p),?_,rightBaire_pair _ _⟩
      simpa only [Set.mem_ofPred_eq,leftBaire_pair,rightBaire_pair,pairBaire_left_right] using hp
  rwa [heq] at hi

/-- Relations are represented on the entrywise code for their two arguments. -/
def ProjectedRelation (ε : ℕ → ℕ) (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  Projected ε {p | R (leftBaire p) (rightBaire p)}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: corollary
  title: Relational images at a fixed parameter
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take the inverse image of $A$ under the first coordinate projection, intersect it with the coded relation,
    and then project to the second coordinate. These three constructions all preserve the fixed parameter.
    A point in the resulting image supplies $x\in A$ and $R(x,y)$; conversely such an $x$ gives the coded point
    $\NamePair{x}{y}$ in the intersection. For an equivalence relation, this is the construction of its
    saturation of $A$.
    \end{proof}
-/
theorem projected_relationalImage {ε : ℕ → ℕ}
    {R : (ℕ → ℕ) → (ℕ → ℕ) → Prop} {A : Set (ℕ → ℕ)}
    (hR : ProjectedRelation ε R) (hA : Projected ε A) :
    Projected ε {y | ∃ x ∈ A, R x y} := by
  have hi := (hR.inter hA.leftPreimage).projectRight
  have heq : rightBaire '' ({p | R (leftBaire p) (rightBaire p)} ∩ (leftBaire ⁻¹' A)) =
      {y | ∃ x ∈ A, R x y} := by
    ext y
    constructor
    · rintro ⟨p,⟨hr,ha⟩,rfl⟩
      exact ⟨leftBaire p,ha,hr⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨pairBaire x y,by simpa only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,
        leftBaire_pair,rightBaire_pair] using And.intro hxy hx,rightBaire_pair x y⟩
  rwa [heq] at hi
end LambdaTree
end PolishSpaceBook
