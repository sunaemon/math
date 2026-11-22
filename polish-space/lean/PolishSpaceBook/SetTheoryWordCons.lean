module

public import PolishSpaceBook.SetTheoryPredicateReflection
public import PolishSpaceBook.SetTheoryNaturalPairing

@[expose] public section

/-! # Prepending an entry to a finite word in the membership language -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Every coordinate is either the new initial entry or a shifted tail entry. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    We first express prepending an entry without invoking an external operation on lists. For $a\in\omega$ and
    $g,h\in F$, put
    $$\begin{aligned}
    K(a,g,h)\;:\equiv\;\forall i,v\in\omega\;\bigl[\Pair{i}{v}\in h
    \longleftrightarrow{}& (i=0\land v=a)\\
     &{}\lor\exists j\in\omega\;(i=j\cup\{j\}\land\Pair{j}{v}\in g)\bigr].
    \end{aligned}$$
    The coordinates of both finite graphs lie in $\omega$, so this condition determines every member of $h$.
    The successor, pair-membership, and equality predicates have their previous first-order expansions.
-/
def SetWordCons (Ω z a s t : ZFSet.{u}) : Prop :=
  ∀ i ∈ Ω, ∀ v ∈ Ω, pair i v ∈ t ↔
    (i = z ∧ v = a) ∨ ∃ j ∈ Ω, i = insert j j ∧ pair j v ∈ s

/-- Parameters omega, zero, head, tail graph, resulting graph. -/
def wordConsPredicate : BoundedSetPredicate 5 :=
  .all 0 (.all 0 (.iff (.pairMember 4 5 6) (.disj (.conj (.equal 5 1) (.equal 6 2))
    (.ex 0 (.conj (.successor 5 7) (.pairMember 3 7 6))))))

def wordConsFormula : ForcingFormulas.Formula 5 := wordConsPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    All quantified indices and values lie in the actual $\omega$ inside the transitive model, which
    also proves the assertion about internal interpretation.
-/
lemma realize_wordConsFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω z a s t : M) :
    wordConsFormula.Realize Empty.elim ![Ω, z, a, s, t] ↔
      SetWordCons Ω.val z.val a.val s.val t.val :=
  wordConsPredicate.realize_compile hM ![Ω, z, a, s, t]

lemma pair_mem_wordGraph_cons (a : ℕ) (s : List ℕ) (i v : ℕ) :
    pair (natOrdinal i) (natOrdinal v) ∈ (wordGraph (a :: s) : ZFSet.{u}) ↔
      (i = 0 ∧ v = a) ∨ ∃ j : ℕ, i = j + 1 ∧ pair (natOrdinal j) (natOrdinal v) ∈ wordGraph s := by
  cases i with
  | zero => simp [pair_mem_wordGraph, eq_comm]
  | succ i => simp [pair_mem_wordGraph]

/-- The first-order coordinate condition is exactly list cons on finite graphs. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal recognition of list cons
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    At coordinate $0$, the graph of $a::s$ contains exactly the value $a$. At coordinate $j+1$, it contains precisely
    the value at coordinate $j$ of $s$, if that coordinate is present. Thus its pair-membership condition is exactly
    $K$. Conversely, $K$ identifies every pair of the two finite graphs, so their equality and injectivity of $e$
    give $t=a::s$.
-/
theorem setWordCons_wordGraph_iff (a : ℕ) (s t : List ℕ) :
    SetWordCons.{u} Ordinal.omega0.toZFSet (natOrdinal 0) (natOrdinal a) (wordGraph s) (wordGraph t) ↔
      t = a :: s := by
  simp only [SetWordCons, forall_mem_omegaOrdinal.{u}, exists_mem_omegaOrdinal.{u},
    ← natOrdinal_succ.{u}, natOrdinal_injective.{u}.eq_iff]
  constructor
  · intro h
    apply wordGraph_injective.{u}
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      obtain ⟨i, rfl⟩ := mem_wordGraph.{u}.mp hp
      exact (pair_mem_wordGraph_cons.{u} a s i.val (t.get i)).mpr
        ((h i.val (t.get i)).mp (mem_wordGraph.{u}.mpr ⟨i, rfl⟩))
    · intro hp
      obtain ⟨i, rfl⟩ := mem_wordGraph.{u}.mp hp
      exact (h i.val ((a :: s).get i)).mpr
        ((pair_mem_wordGraph_cons.{u} a s i.val ((a :: s).get i)).mp (mem_wordGraph.{u}.mpr ⟨i, rfl⟩))
  · rintro rfl
    exact fun i v => pair_mem_wordGraph_cons.{u} a s i v

end PolishSpaceBook.SetTheoryModels
