module

public import PolishSpaceBook.SetTheoryNaturalMultiplication
public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.LambdaNumericalPairing

@[expose] public section

/-! # The book's natural-number pairing and projections inside a transitive model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma natOrdinal_mem_natOrdinal (i j : ℕ) :
    (natOrdinal i : ZFSet.{u}) ∈ natOrdinal j ↔ i < j := by
  rw [mem_natOrdinal]
  exact ⟨fun ⟨k, hk, he⟩ => natOrdinal_injective he ▸ hk, fun h => ⟨i, h, rfl⟩⟩

/-- Parameters omega, addition graph, multiplication graph, i,j,k. -/
def naturalPairingPredicate : BoundedSetPredicate 6 :=
  .disj (.conj (.member 3 4) (.ex 0
    (.conj (binaryMemberAt 2 4 4 6) (binaryMemberAt 1 6 3 5))))
    (.conj (.neg (.member 3 4)) (.ex 0 (.ex 0
      (.conj (binaryMemberAt 2 3 3 6)
        (.conj (binaryMemberAt 1 6 3 7) (binaryMemberAt 1 7 4 5))))))

def naturalPairingFormula : ForcingFormulas.Formula 6 := naturalPairingPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Use the formula
    $$p(i,j)=\begin{cases}j^2+i,&i<j,\\i^2+i+j,&j\le i.\end{cases}$$
    For finite ordinals, $i<j$ is exactly $i\in j$. In the first case, quantify a natural number equal to $j\cdot j$
    using $\Gamma_\times$, then add $i$ using $\Gamma_+$. In the other case, quantify the intermediate values of
    $i\cdot i$ and $i^2+i$, then add $j$. Every intermediate value is in the actual $\omega$, so the formula recognizes
    the displayed pairing internally.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $p(i,j)=\NatPair{i}{j}$ for the numerical pairing of §{sec:lambda-numerical-pairing}. Its value is a natural
    number; the pairs used to store function graphs above are set-theoretic ordered pairs.
-/
lemma eval_naturalPairingPredicate (i j k : ℕ) :
    naturalPairingPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a + b), naturalBinaryGraph (fun a b => a * b),
      natOrdinal i, natOrdinal j, natOrdinal k] ↔ k = Nat.pair i j := by
  by_cases h : i < j <;>
    simp [naturalPairingPredicate, BoundedSetPredicate.eval, eval_binaryMemberAt, Fin.snoc, Fin.castLT,
      exists_mem_omegaOrdinal, pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff,
      h, Nat.pair]

lemma naturalPairing_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω A P a b c : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hA : A.val = naturalBinaryGraph (fun i j => i + j))
    (hP : P.val = naturalBinaryGraph (fun i j => i * j))
    (i j k : ℕ) (ha : a.val = natOrdinal i) (hb : b.val = natOrdinal j) (hc : c.val = natOrdinal k) :
    naturalPairingFormula.Realize Empty.elim ![Ω, A, P, a, b, c] ↔ k = Nat.pair i j := by
  rw [naturalPairingFormula, naturalPairingPredicate.realize_compile hM]
  have he : Subtype.val ∘ ![Ω, A, P, a, b, c] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun i j => i + j),
        naturalBinaryGraph (fun i j => i * j), natOrdinal i, natOrdinal j, natOrdinal k] := by
    funext t; fin_cases t <;> simp [Function.comp_apply, hΩ, hA, hP, ha, hb, hc]
  rw [he, eval_naturalPairingPredicate]

/-- The actual square-shell pairing graph is internal. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal numerical pairing and projections
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separation gives $\Gamma_p\in M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The counterexample-tree tests use numerical pairing, its projections, and finite-list codes. Their lambda
    implementations were given in §{sec:lambda-numerical-pairing} and §{sec:lambda-finite-lists}. To use these tests
    inside a model, we must also construct their set-coded graphs internally. We begin with the arithmetic and
    pairing operations. In this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set,
    and Separation; Choice and Replacement are not needed for these constructions.
-/
theorem naturalPairingGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (naturalBinaryGraph Nat.pair : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let A : M := ⟨naturalBinaryGraph (fun i j => i + j), naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let P : M := ⟨naturalBinaryGraph (fun i j => i * j), naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep⟩
  apply naturalBinaryGraph_mem hM hpair hunion hpower hsep naturalPairingFormula Ω A P rfl
  intro x y z i j k hx hy hz
  exact naturalPairing_absolute hM Ω A P x y z rfl rfl rfl i j k hx hy hz

/-- Parameters omega, pairing graph, output pair; all witnesses are bounded by omega. -/
def naturalProjectionPredicate (first : Bool) : BoundedSetPredicate 3 :=
  .ex 0 (.ex 0 (.ex 0 (.conj (binaryMemberAt 1 3 4 5)
    (.orderedPair 2 5 (if first then 3 else 4)))))

def naturalProjectionFormula (first : Bool) : ForcingFormulas.Formula 3 :=
  (naturalProjectionPredicate first).compile

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The pairing bijection proved in §{sec:lambda-numerical-pairing} makes both graphs total and single-valued, and
    identifies their values with the numerical projections used in the finite tests. The quantified witnesses are
    natural numbers, so internal and external interpretations agree.
-/
lemma eval_naturalProjectionPredicate (first : Bool) (p : ZFSet.{u}) :
    (naturalProjectionPredicate first).eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph Nat.pair, p] ↔
      p ∈ sequenceGraph (fun n => natOrdinal (if first then n.unpair.1 else n.unpair.2)) := by
  have he : (naturalProjectionPredicate first).eval
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph Nat.pair, p] ↔
      ∃ i j : ℕ, p = pair (natOrdinal (Nat.pair i j)) (natOrdinal (if first then i else j)) := by
    cases first <;>
      simp [naturalProjectionPredicate, BoundedSetPredicate.eval, eval_binaryMemberAt, Fin.snoc, Fin.castPred, Fin.castLT,
        exists_mem_omegaOrdinal, pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff]
  rw [he]
  constructor
  · rintro ⟨i, j, rfl⟩
    simp only [pair_mem_sequenceGraph, NamedLambda.AlphaTerm.squarePair_decode_encode]
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact ⟨n.unpair.1, n.unpair.2, by rw [NamedLambda.AlphaTerm.squarePair_encode_decode]⟩

/-- Both numerical decoding projections reuse bounded reflection and subset collection. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal numerical pairing and projections
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The inverse-projection graphs are separated from $\omega\times\omega$ as
    $$\begin{aligned}
    Q_1&:=\{\langle z,i\rangle:z,i\in\omega,\ \exists j\in\omega\;
    \langle\langle i,j\rangle,z\rangle\in\Gamma_p\},\\
    Q_2&:=\{\langle z,j\rangle:z,j\in\omega,\ \exists i\in\omega\;
    \langle\langle i,j\rangle,z\rangle\in\Gamma_p\}.
    \end{aligned}$$
-/
theorem naturalProjectionGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (first : Bool) :
    sequenceGraph (fun n => natOrdinal (if first then n.unpair.1 else n.unpair.2)) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let P : M := ⟨naturalBinaryGraph Nat.pair, naturalPairingGraph_mem hM hinf hpair hunion hpower hsep⟩
  apply (naturalProjectionPredicate first).subset_mem hM (hsep _) ![Ω, P]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨_, rfl⟩)).1
  intro p _
  have he : Fin.snoc (Subtype.val ∘ ![Ω, P]) p =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph Nat.pair, p] := by funext i; fin_cases i <;> rfl
  rw [he, eval_naturalProjectionPredicate]

end PolishSpaceBook.SetTheoryModels
