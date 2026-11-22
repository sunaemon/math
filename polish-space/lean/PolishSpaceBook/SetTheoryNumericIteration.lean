module

public import PolishSpaceBook.SetTheoryInternalIteration
public import PolishSpaceBook.SetTheoryPredicateComposition

@[expose] public section

/-! # Internal formulas for iteration on the actual natural numbers -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters omega, next-state graph, initial value, zero, sequence graph. -/
def numericIterationPredicate : BoundedSetPredicate 5 :=
  .conj (.function 0 0 4) (.conj (.pairMember 4 3 2)
    (.all 0 (.all 0 (.all 0 (.all 0
      (BoundedSetPredicate.imply
        (.conj (.successor 6 5) (.conj (.pairMember 4 5 7) (.pairMember 4 6 8)))
        (.pairMember 1 7 8)))))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For a function graph $d:\omega\to\omega$, define the first-order formulas
    $$\begin{aligned}
    I(d,a,g)\;:\equiv\;&g:\omega\to\omega\land\langle0,a\rangle\in g\\
     &{}\land\forall n,k,x,y\in\omega\;\bigl[\bigl(k=n\cup\{n\}\\
     &\qquad{}\land\langle n,x\rangle\in g\land\langle k,y\rangle\in g\bigr)
     \longrightarrow\langle x,y\rangle\in d\bigr],\\
    V(d,a,n,y)\;:\equiv\;&\exists g\;\bigl(I(d,a,g)\land\langle n,y\rangle\in g\bigr).
    \end{aligned}$$
    The parameter $\omega$ denotes the actual set constructed inside the model. Expand the function, pair-membership,
    and successor predicates by their earlier definitions. In particular, the existential quantifier over $g$ in
    $M\models V(d,a,n,y)$ ranges only over graphs belonging to $M$.
-/
def numericIterationFormula : ForcingFormulas.Formula 5 := numericIterationPredicate.compile

lemma numericIterationFormula_deltaZero : IsDeltaZero numericIterationFormula :=
  numericIterationPredicate.compile_deltaZero

def IsNumericIteration (Ω d a z g : ZFSet.{u}) : Prop :=
  IsFunc Ω Ω g ∧ pair z a ∈ g ∧
    ∀ n ∈ Ω, ∀ k ∈ Ω, ∀ x ∈ Ω, ∀ y ∈ Ω,
      k = insert n n → pair n x ∈ g → pair k y ∈ g → pair x y ∈ d

lemma realize_numericIterationFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω d a z g : M) :
    numericIterationFormula.Realize Empty.elim ![Ω, d, a, z, g] ↔
      IsNumericIteration Ω.val d.val a.val z.val g.val := by
  simpa [numericIterationFormula, numericIterationPredicate, BoundedSetPredicate.eval,
    BoundedSetPredicate.imply, IsNumericIteration, Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT,
    or_iff_not_imp_left] using numericIterationPredicate.realize_compile hM ![Ω, d, a, z, g]

/-- Recognize each value without assuming the whole external graph is internal. -/
lemma IsNumericIteration.value {d g : ZFSet.{u}} {f : ℕ → ℕ} {a : ℕ}
    (hd : IsFunc Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet d)
    (hfd : ∀ n, pair (natOrdinal n) (natOrdinal (f n)) ∈ d)
    (hg : IsNumericIteration Ordinal.omega0.toZFSet d (natOrdinal a) (natOrdinal 0) g) (n : ℕ) :
    pair (natOrdinal n) (natOrdinal (f^[n] a)) ∈ g := by
  induction n with
  | zero => exact hg.2.1
  | succ n ih =>
    have hn (k : ℕ) : natOrdinal k ∈ Ordinal.omega0.toZFSet := mem_omegaOrdinal.mpr ⟨k, rfl⟩
    obtain ⟨y, hy, _⟩ := hg.1.2 _ (hn (n + 1))
    have hyΩ := (ZFSet.pair_mem_prod.mp (hg.1.1 hy)).2
    have hdy := hg.2.2 _ (hn n) _ (hn (n + 1)) _ (hn _) y hyΩ (natOrdinal_succ n) ih hy
    have he := (hd.2 _ (hn (f^[n] a))).unique hdy (hfd (f^[n] a))
    rw [he] at hy
    simpa only [Function.iterate_succ_apply'] using hy

lemma numericIteration_sequenceGraph (d : ZFSet.{u}) (f : ℕ → ℕ) (a : ℕ)
    (hfd : ∀ n, pair (natOrdinal n) (natOrdinal (f n)) ∈ d) :
    IsNumericIteration Ordinal.omega0.toZFSet d (natOrdinal a) (natOrdinal 0)
      (sequenceGraph (fun n => natOrdinal (f^[n] a))) := by
  have hn (n : ℕ) : natOrdinal n ∈ Ordinal.omega0.toZFSet := mem_omegaOrdinal.mpr ⟨n, rfl⟩
  refine ⟨sequenceGraph_isFunc _ (fun n => hn _), (pair_mem_sequenceGraph _ 0 _).mpr rfl, ?_⟩
  intro n hn' k _ x _ y _ hsucc hnx hky
  obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp hn'
  rw [← natOrdinal_succ] at hsucc
  subst k
  have hx := (pair_mem_sequenceGraph _ i x).mp hnx
  have hy := (pair_mem_sequenceGraph _ (i + 1) y).mp hky
  rw [hx, hy, Function.iterate_succ_apply']
  exact hfd _

lemma numericIterationGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (d : M) (f : ℕ → ℕ)
    (hd : IsFunc Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet d.val)
    (hfd : ∀ n, pair (natOrdinal n) (natOrdinal (f n)) ∈ d.val) (a : ℕ) :
    sequenceGraph (fun n => natOrdinal (f^[n] a)) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) : natOrdinal n ∈ Ω.val := mem_omegaOrdinal.mpr ⟨n, rfl⟩
  obtain ⟨s, h0, hs, hstep, hg⟩ := internal_function_iteration hM hinf hpair hunion hpower hsep
    Ω d hd ⟨natOrdinal a, hn a⟩
  have he (n : ℕ) : s n = natOrdinal (f^[n] a) := by
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hh := hstep n
      rw [ih] at hh
      have he := (hd.2 _ (hn _)).unique hh (hfd (f^[n] a))
      simpa only [Function.iterate_succ_apply'] using he
  have hfun : s = fun n => natOrdinal (f^[n] a) := funext he
  exact hfun ▸ hg

/-- Parameters omega,d,zero,a,n,y; the witness is the complete iteration graph. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For a function graph $d:\omega\to\omega$, define the first-order formulas
    $$\begin{aligned}
    I(d,a,g)\;:\equiv\;&g:\omega\to\omega\land\langle0,a\rangle\in g\\
     &{}\land\forall n,k,x,y\in\omega\;\bigl[\bigl(k=n\cup\{n\}\\
     &\qquad{}\land\langle n,x\rangle\in g\land\langle k,y\rangle\in g\bigr)
     \longrightarrow\langle x,y\rangle\in d\bigr],\\
    V(d,a,n,y)\;:\equiv\;&\exists g\;\bigl(I(d,a,g)\land\langle n,y\rangle\in g\bigr).
    \end{aligned}$$
    The parameter $\omega$ denotes the actual set constructed inside the model. Expand the function, pair-membership,
    and successor predicates by their earlier definitions. In particular, the existential quantifier over $g$ in
    $M\models V(d,a,n,y)$ ranges only over graphs belonging to $M$.
-/
def numericIterationValueFormula : ForcingFormulas.Formula 6 :=
  ((reindex numericIterationFormula ![(0 : Fin 7), 1, 3, 2, 6]) ⊓ pairMemberFormula 6 4 5).ex

lemma realize_numericIterationValueFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω d z a n y : M) :
    numericIterationValueFormula.Realize Empty.elim ![Ω, d, z, a, n, y] ↔
      ∃ g : M, IsNumericIteration Ω.val d.val a.val z.val g.val ∧ pair n.val y.val ∈ g.val := by
  simp only [numericIterationValueFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, realize_pairMemberFormula_model hM]
  have he (g : M) : (Fin.snoc ![Ω, d, z, a, n, y] g) ∘ ![(0 : Fin 7), 1, 3, 2, 6] =
      ![Ω, d, a, z, g] := by funext i; fin_cases i <;> rfl
  simp only [he, realize_numericIterationFormula hM]
  rfl

/-- The internal value formula computes the actual natural iterate. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal recognition of numerical iteration
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    If an internal graph $g$ witnesses the left side, transitivity makes it an actual function on $\omega$ satisfying
    $I(d,a,g)$. Induction gives $\langle n,f^n(a)\rangle\in g$: the initial clause gives the base case, and totality of
    $g$ together with the successor clause and uniqueness of the value of $d$ gives the next value. Since $g$ also
    contains $\langle n,y\rangle$, functionality gives $y=f^n(a)$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, the iteration lemma of §{sec:internal-tree-branches} constructs the whole graph of
    $n\mapsto f^n(a)$ inside $M$. It satisfies $I(d,a,g)$ and witnesses the value formula. Thus the converse does not
    assume that an externally defined infinite graph is automatically internal.
-/
theorem numericIterationValue_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (Ω d z a n y : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hz : z.val = natOrdinal 0)
    (f : ℕ → ℕ) (hd : IsFunc Ω.val Ω.val d.val)
    (hfd : ∀ k, pair (natOrdinal k) (natOrdinal (f k)) ∈ d.val)
    (i j k : ℕ) (ha : a.val = natOrdinal i) (hn : n.val = natOrdinal j) (hy : y.val = natOrdinal k) :
    numericIterationValueFormula.Realize Empty.elim ![Ω, d, z, a, n, y] ↔ k = f^[j] i := by
  rw [realize_numericIterationValueFormula hM]
  rw [hΩ] at hd
  constructor
  · rintro ⟨g, hg, hny⟩
    rw [hΩ, ha, hz] at hg
    rw [hn, hy] at hny
    have he := (hg.1.2 _ (mem_omegaOrdinal.mpr ⟨j, rfl⟩)).unique hny (hg.value hd hfd j)
    exact natOrdinal_injective he
  · intro hk
    let g := sequenceGraph (fun n => natOrdinal (f^[n] i))
    have hg := numericIterationGraph_mem hM hinf hpair hunion hpower hsep d f hd hfd i
    refine ⟨⟨g, hg⟩, ?_, ?_⟩
    · rw [hΩ, ha, hz]
      exact numericIteration_sequenceGraph d.val f i hfd
    · rw [hn, hy, hk]
      exact (pair_mem_sequenceGraph _ j _).mpr rfl

end PolishSpaceBook.SetTheoryModels
