module

public import PolishSpaceBook.LambdaUniformDeciders
public import PolishSpaceBook.CantorDerivativeCoding

@[expose] public section

/-! # A uniform lambda program for guarded intersections of closed-tree codes

The same program handles all rows of the family. One universal-quantifier
compiler then decides their guarded intersection at one jump. Choosing
separate deciders for each row would not suffice for this construction.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace CantorDerivative
set_option maxHeartbeats 400000

def negationProgram (P : AlphaTerm) : AlphaTerm := mapOutputProgram reverseZeroTerm P

def intersectionMatrixProgram (P Q C : AlphaTerm) : AlphaTerm :=
  conjunctionProgram (reindexProgram P (numericalProjectionTerm true))
    (negationProgram (conjunctionProgram (reindexProgram C (numericalProjectionTerm false))
      (negationProgram (reindexProgram Q
        (pairNumerical (numericalProjectionTerm false) (numericalProjectionTerm true))))))

theorem intersectionMatrixProgram_closed {P Q C : AlphaTerm}
    (hP : P.Closed) (hQ : Q.Closed) (hC : C.Closed) :
    (intersectionMatrixProgram P Q C).Closed := by
  apply conjunctionProgram_closed
  · exact reindexProgram_closed hP (projection_computes true).1
  · apply mapOutputProgram_closed reverseZero_computes.1
    apply conjunctionProgram_closed
    · exact reindexProgram_closed hC (projection_computes false).1
    · exact mapOutputProgram_closed reverseZero_computes.1
        (reindexProgram_closed hQ ((projection_computes false).pair (projection_computes true)).1)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The projections and pairing term first recover the two input numbers and put them in the order
    expected by the family decider. The given programs terminate on every input and return bits.
    The term $J$ returns zero precisely when the index is retained and the family test fails.
    Multiplication with the initial-tree bit therefore decides the matrix in
    §{sec:edst-effective-cb}. Beta/query reductions lift through these applications, always retaining the
    same input function. The universal-quantifier compiler proves the claimed jump bound. If the set
    of retained indices is empty, the implication bit is always one and the result is just the initial
    tree; no nonemptiness or witness-selection assumption is used.
    \end{proof}
-/
theorem intersectionMatrixProgram_decides {ε : ℕ → ℕ} {P Q C : AlphaTerm}
    {T : ℕ → Prop} {S : ℕ → ℕ → Prop} {G : ℕ → Prop}
    (hP : Decides ε P T) (hQ : Decides ε Q (fun z : ℕ => S z.unpair.1 z.unpair.2))
    (hC : Decides ε C G) :
    Decides ε (intersectionMatrixProgram P Q C)
      (fun z : ℕ => T z.unpair.1 ∧ (G z.unpair.2 → S z.unpair.2 z.unpair.1)) := by
  have hp := hP.precompNumerical (projection_computes true)
    (g := fun z : ℕ => z.unpair.1) (by simp)
  have hc := hC.precompNumerical (projection_computes false)
    (g := fun z : ℕ => z.unpair.2) (by simp)
  have hq := hQ.precompNumerical ((projection_computes false).pair (projection_computes true))
    (g := fun z : ℕ => Nat.pair z.unpair.2 z.unpair.1) (by simp)
  have h := conjunctionProgram_decides hp (conjunctionProgram_decides hc hq.negate).negate
  simpa only [intersectionMatrixProgram,negationProgram,Nat.unpair_pair,not_and,not_not] using h

/-- One fixed compiled term works for all input parameters and all decided families. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let closed terms $P,Q,C$ decide respectively the initial-tree predicate, the joint family predicate,
    and the set of retained indices. The input to $Q$ is $\NatPair{b}{s}$, whereas the quantified matrix
    uses $z=\NatPair{s}{b}$. Abbreviate
    $$s(z):=\LambdaNumericProjection{1}\,z,\qquad b(z):=\LambdaNumericProjection{2}\,z.$$
    Let $Z:=\lambdaab{x}{\LambdaZeroTest\,x\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$ reverse a decision bit,
    and form
    $$\begin{aligned}
     H&:=\lambdaab{o}{\lambdaab{z}{Qo(\LambdaNumericPair\,b(z)\,s(z))}},\\
     J&:=\lambdaab{o}{\lambdaab{z}{Z\bigl(\LambdaMul\,(Co\,b(z))\,(Z(Hoz))\bigr)}},\\
     M&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(Po\,s(z))\,(Joz)}}.
    \end{aligned}$$
    Expand these abbreviations with fresh binders. If $e$ is the syntax index of $M$, the program with
    index $\upsilon(e)$ from §{sec:lambda-relative-jump} decides the guarded intersection at one jump.
    This program is fixed before the input parameter is supplied.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Uniform guarded tree intersections
-/
theorem guarded_intersection_program (P Q C : AlphaTerm)
    (hP : P.Closed) (hQ : Q.Closed) (hC : C.Closed) :
    ∃ L : AlphaTerm, L.Closed ∧ ∀ (ε : ℕ → ℕ) (T : ℕ → Prop)
      (S : ℕ → ℕ → Prop) (G : ℕ → Prop),
      Decides ε P T → Decides ε Q (fun z : ℕ => S z.unpair.1 z.unpair.2) →
      Decides ε C G → Decides (jumpName ε) L (fun s => T s ∧ ∀ b, G b → S b s) := by
  obtain ⟨L,hL,hu⟩ := exists_universal_jump_program (intersectionMatrixProgram P Q C)
    (intersectionMatrixProgram_closed hP hQ hC)
  refine ⟨L,hL,fun ε T S G hp hq hc => ?_⟩
  have h := hu ε (fun s b => T s ∧ (G b → S b s))
    (intersectionMatrixProgram_decides hp hq hc)
  convert h using 1
  funext s
  apply propext
  constructor
  · rintro ⟨hs,h⟩ b; exact ⟨hs,h b⟩
  · intro h; exact ⟨(h 0).1,fun b => (h b).2⟩

def guardedIntersection (T : Set (List Bool)) (S : ℕ → Set (List Bool)) (G : ℕ → Prop) :
    Set (List Bool) := T ∩ {s | ∀ b, G b → s ∈ S b}

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Uniform guarded tree intersections
-/
theorem guardedIntersection_isSubtree {T : Set (List Bool)} {S : ℕ → Set (List Bool)}
    {G : ℕ → Prop} (hT : IsSubtree T) (hS : ∀ b, G b → IsSubtree (S b)) :
    IsSubtree (guardedIntersection T S G) := by
  intro s t ht hst
  exact ⟨hT ht.1 hst,fun b hb => hS b hb (ht.2 b hb) hst⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The tree and body assertions follow from intersections. Numerically, membership is
    $$s\in T\ \land\ \forall b\in\NN\ \bigl(b\in G\Longrightarrow s\in S_b\bigr).$$
    Use the total matrix
    $$s\in T\ \land\ \bigl(b\in G\Longrightarrow s\in S_b\bigr)$$
    and apply the universal-quantifier compiler once. Repeating the initial-tree test under the
    quantifier gives exactly the desired conjunction, since the numerical quantifier has a nonempty
    domain. §{sec:lambda-cantor-derivative-programs} gives the closed term and its reductions.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Uniform guarded tree intersections
-/
theorem guardedIntersection_body (T : Set (List Bool)) (S : ℕ → Set (List Bool)) (G : ℕ → Prop) :
    treeBody (guardedIntersection T S G) = treeBody T ∩ {x | ∀ b, G b → x ∈ treeBody (S b)} := by
  ext x
  constructor
  · intro hx
    exact ⟨fun n => (hx n).1,fun b hb n => (hx n).2 b hb⟩
  · rintro ⟨hxT,hxS⟩ n
    exact ⟨hxT n,fun b hb => hxS b hb n⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Uniform guarded tree intersections
-/
theorem guardedIntersection_decidable {ε : ℕ → ℕ} {T : Set (List Bool)}
    {S : ℕ → Set (List Bool)} {G : ℕ → Prop}
    (hT : DecidablePredicate ε (fun s : ℕ => decodeWord s ∈ T))
    (hS : DecidablePredicate ε (fun z : ℕ => decodeWord z.unpair.2 ∈ S z.unpair.1))
    (hG : DecidablePredicate ε G) :
    DecidablePredicate (jumpName ε) (fun s : ℕ => decodeWord s ∈ guardedIntersection T S G) := by
  obtain ⟨P,hP⟩ := hT
  obtain ⟨Q,hQ⟩ := hS
  obtain ⟨C,hC⟩ := hG
  obtain ⟨L,_,hL⟩ := guarded_intersection_program P Q C hP.1 hQ.1 hC.1
  exact ⟨L,hL ε _ _ _ hP hQ hC⟩

end CantorDerivative
end PolishSpaceBook
