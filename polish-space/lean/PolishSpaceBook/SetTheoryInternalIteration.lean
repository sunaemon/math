module

public import PolishSpaceBook.SetTheoryInternalFixedPoint
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section


/-! # Internal graphs of natural-number iteration

A least fixed point on omega times the state set contains the initial pair and
is closed under the next-state graph. Induction identifies every finite level,
so the whole external iteration graph belongs to the model.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters omega, states, transition, initial state, zero, candidate, output. -/
def iterationStepPredicate : BoundedSetPredicate 7 :=
  .disj (.orderedPair 6 4 3)
    (.ex 0 (.ex 0 (.ex 1 (.ex 1
      (.conj (.successor 8 7) (.conj (.orderedPair 6 8 10)
        (.conj (.pairMember 5 7 9) (.pairMember 2 9 10))))))))

def iterationStepFormula : ForcingFormulas.Formula 7 :=
  iterationStepPredicate.compile

lemma iterationStepFormula_deltaZero : IsDeltaZero iterationStepFormula :=
  iterationStepPredicate.compile_deltaZero

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    The actual set $\omega$ belongs to $M$, and so does $D=\omega\times B$. On subsets of $D$, use the operation
    $$\begin{aligned}
    \Phi(C):={}&\{\langle 0,a\rangle\}\\
     &{}\cup\{\langle k,y\rangle:n,k\in\omega,\ x,y\in B,\ k=n+1,\\
     &\hspace{40mm}\langle n,x\rangle\in C,\ \langle x,y\rangle\in d\}.
    \end{aligned}$$
-/
def iterationStep (Ω B c a z C p : ZFSet.{u}) : Prop :=
  p = pair z a ∨ ∃ n ∈ Ω, ∃ k ∈ Ω, ∃ x ∈ B, ∃ y ∈ B,
    k = insert n n ∧ p = pair k y ∧ pair n x ∈ C ∧ pair x y ∈ c

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The displayed predicate is first-order definable using the pair and
    successor formulas, with all witnesses bounded by $\omega$ or $B$. Transitivity therefore identifies its internal
    interpretation with the displayed operation.
-/
lemma realize_iterationStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω B c a z C p : M) :
    iterationStepFormula.Realize Empty.elim ![Ω, B, c, a, z, C, p] ↔
      iterationStep Ω.val B.val c.val a.val z.val C.val p.val := by
  simpa [iterationStepFormula, iterationStepPredicate, BoundedSetPredicate.eval,
    iterationStep, Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT] using
    iterationStepPredicate.realize_compile hM ![Ω, B, c, a, z, C, p]

/-- Set-code a sequence of arbitrary sets by its graph on the finite ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For a sequence of sets $s:\omega\to B$,
    write its function graph as
    $$G_s:=\{\langle n,s(n)\rangle:n\in\omega\}.$$
-/
def sequenceGraph (s : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n => pair (natOrdinal n) (s n))

lemma pair_mem_sequenceGraph (s : ℕ → ZFSet.{u}) (n : ℕ) (y : ZFSet.{u}) :
    pair (natOrdinal n) y ∈ sequenceGraph s ↔ y = s n := by
  rw [sequenceGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hn, hy⟩ := ZFSet.pair_inj.mp hk
    have hn' := natOrdinal_injective hn
    simpa only [hn'] using hy.symm
  · rintro rfl
    exact ⟨n, rfl⟩

lemma sequenceGraph_isFunc {B : ZFSet.{u}} (s : ℕ → ZFSet.{u}) (hs : ∀ n, s n ∈ B) :
    IsFunc Ordinal.omega0.toZFSet B (sequenceGraph s) := by
  constructor
  · intro p hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨n, rfl⟩, hs n⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp hn
    exact ⟨s k, (pair_mem_sequenceGraph s k _).mpr rfl,
      fun y hy => (pair_mem_sequenceGraph s k y).mp hy⟩

/-- The whole graph is internal, not merely each of its finite values. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal iteration on natural numbers
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    It is monotone and takes values in $D$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The internal least-fixed-point theorem in
    §{sec:internal-model-fixed-points} uses only Separation once $D$ and the parameters belong to $M$.
    It gives $C\in M$ with $C=\Phi(C)$. Thus this construction uses neither Replacement nor Choice.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Induction on $n$ proves
    $$\langle n,y\rangle\in C\quad\Longleftrightarrow\quad y=s(n).$$
    At $n=0$, only the initial pair can occur, since no natural number has successor $0$. At $n+1$, only the successor
    clause can occur. Its predecessor index must be $n$, its preceding value must be $s(n)$ by induction, and the
    function graph $d$ determines its next value uniquely. Conversely, that successor clause inserts precisely the
    required pair. Since $C\IncludedIn\omega\times B$, these identities prove $C=G_s$.
-/
theorem internal_function_iteration {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (B c : M) (hc : IsFunc B.val B.val c.val) (a : B.val) :
    ∃ s : ℕ → ZFSet.{u}, s 0 = a.val ∧ (∀ n, s n ∈ B.val) ∧
      (∀ n, pair (s n) (s (n + 1)) ∈ c.val) ∧ sequenceGraph s ∈ M := by
  let next : B.val → B.val := fun x =>
    ⟨(hc.2 x.val x.property).choose, (ZFSet.pair_mem_prod.mp
      (hc.1 (hc.2 x.val x.property).choose_spec.1)).2⟩
  have hnext (x : B.val) : pair x.val (next x).val ∈ c.val :=
    (hc.2 x.val x.property).choose_spec.1
  let v : ℕ → B.val := fun n => next^[n] a
  have hv0 : v 0 = a := rfl
  have hvs (n : ℕ) : v (n + 1) = next (v n) := Function.iterate_succ_apply' next n a
  let s : ℕ → ZFSet.{u} := fun n => (v n).val
  have hs (n : ℕ) : s n ∈ B.val := (v n).property
  have hsc (n : ℕ) : pair (s n) (s (n + 1)) ∈ c.val := by
    change pair (v n).val (v (n + 1)).val ∈ c.val
    rw [hvs]
    exact hnext (v n)
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let z : M := ⟨natOrdinal 0, natOrdinal_zero.symm ▸ empty_mem_of_infinity hM hinf⟩
  let aM : M := ⟨a.val, hM.mem_trans a.property B.property⟩
  let D : M := ⟨ZFSet.prod Ω.val B.val,
    prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property B.property⟩
  let step := iterationStep Ω.val B.val c.val a.val z.val
  obtain ⟨hC, hfix⟩ := internal_definable_fixed_point hM hsep iterationStepFormula
    ![Ω, B, c, aM, z] D step (by
      intro C p _
      have he : Fin.snoc (Fin.snoc ![Ω, B, c, aM, z] C) p = ![Ω, B, c, aM, z, C, p] := by
        funext i
        fin_cases i <;> rfl
      rw [he]
      exact realize_iterationStepFormula hM Ω B c aM z C p) (by
      intro S T hST p _ hp
      rcases hp with hp | ⟨n, hn, k, hk, x, hx, y, hy, he, hp, hnx, hxy⟩
      · exact Or.inl hp
      · exact Or.inr ⟨n, hn, k, hk, x, hx, y, hy, he, hp, hST hnx, hxy⟩)
  let C := internalLeastClosed M D.val step
  have hmem (p : ZFSet.{u}) : p ∈ C ↔ p ∈ D.val ∧ step C p := by
    exact (Iff.of_eq (congrArg (fun S => p ∈ S) hfix).symm).trans ZFSet.mem_sep
  have hn (n : ℕ) : natOrdinal n ∈ Ω.val := mem_omegaOrdinal.mpr ⟨n, rfl⟩
  have hpairval (n : ℕ) : ∀ y, pair (natOrdinal n) y ∈ C ↔ y = s n := by
    induction n with
    | zero =>
      intro y
      constructor
      · intro hy
        rcases (hmem _).mp hy |>.2 with he | ⟨n, hn', k, _, x, _, w, _, hk, hp, _, _⟩
        · exact (ZFSet.pair_inj.mp he).2
        · obtain ⟨j, rfl⟩ := mem_omegaOrdinal.mp hn'
          have he := (ZFSet.pair_inj.mp hp).1.trans hk
          rw [← natOrdinal_succ] at he
          exact False.elim (Nat.noConfusion (natOrdinal_injective he))
      · rintro rfl
        exact (hmem _).mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hn 0, hs 0⟩, Or.inl rfl⟩
    | succ n ih =>
      intro y
      constructor
      · intro hy
        rcases (hmem _).mp hy |>.2 with he | ⟨j, hj, k, _, x, hx, w, _, hk, hp, hjx, hxw⟩
        · have he' := natOrdinal_injective (ZFSet.pair_inj.mp he).1
          exact False.elim (Nat.noConfusion he')
        · obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp hj
          obtain ⟨hki, rfl⟩ := ZFSet.pair_inj.mp hp
          have he := hki.trans hk
          rw [← natOrdinal_succ] at he
          have he' : n = i := Nat.succ.inj (natOrdinal_injective he)
          subst i
          have hx' := (ih x).mp hjx
          subst x
          exact (hc.2 _ (hs n)).unique hxw (hsc n)
      · rintro rfl
        exact (hmem _).mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hn (n + 1), hs (n + 1)⟩,
          Or.inr ⟨natOrdinal n, hn n, natOrdinal (n + 1), hn (n + 1), s n, hs n,
            s (n + 1), hs (n + 1), natOrdinal_succ n, rfl, (ih _).mpr rfl, hsc n⟩⟩
  have he : C = sequenceGraph s := by
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      obtain ⟨n, hn', y, _, rfl⟩ := ZFSet.mem_prod.mp ((hmem p).mp hp).1
      obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp hn'
      exact (pair_mem_sequenceGraph s k y).mpr ((hpairval k y).mp hp)
    · intro hp
      obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
      exact (hpairval n _).mpr rfl
  exact ⟨s, rfl, hs, hsc, he ▸ hC⟩

end PolishSpaceBook.SetTheoryModels
