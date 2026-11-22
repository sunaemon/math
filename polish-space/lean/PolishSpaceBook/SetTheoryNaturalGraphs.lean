module

public import PolishSpaceBook.SetTheoryNumericIteration
public import Mathlib.Order.SuccPred.Nat

@[expose] public section

/-! # Internal graphs of definable operations on natural numbers -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- A binary numerical operation as a graph whose input is an ordered pair. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For a binary numerical operation $F$, encode its graph as
    $$\Gamma_F:=\{\langle\langle m,n\rangle,F(m,n)\rangle:m,n\in\omega\}.$$
-/
def naturalBinaryGraph (f : ℕ → ℕ → ℕ) : ZFSet.{u} :=
  ZFSet.range (fun p : ℕ × ℕ =>
    pair (pair (natOrdinal p.1) (natOrdinal p.2)) (natOrdinal (f p.1 p.2)))

lemma pair_mem_naturalBinaryGraph (f : ℕ → ℕ → ℕ) (i j : ℕ) (z : ZFSet.{u}) :
    pair (pair (natOrdinal i) (natOrdinal j)) z ∈ naturalBinaryGraph f ↔ z = natOrdinal (f i j) := by
  rw [naturalBinaryGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, he⟩
    obtain ⟨hab, hz⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hai, hbj⟩ := ZFSet.pair_inj.mp hab
    have ha := natOrdinal_injective hai
    have hb := natOrdinal_injective hbj
    change a = i at ha
    change b = j at hb
    subst a b
    exact hz.symm
  · rintro rfl
    exact ⟨(i, j), rfl⟩

/-- Three parameters, then the candidate graph element; the first parameter is omega. -/
def naturalBinaryGraphFormula (φ : ForcingFormulas.Formula 6) : ForcingFormulas.Formula 4 :=
  boundedExists 0 (boundedExists 0 (boundedExists 0
    ((orderedPairFormula (7 : Fin 8) 4 5 ⊓ orderedPairFormula 3 7 6 ⊓
      reindex φ ![0, 1, 2, 4, 5, 6]).ex)))

lemma realize_naturalBinaryGraphFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (φ : ForcingFormulas.Formula 6) (Ω P Q p : M) :
    (naturalBinaryGraphFormula φ).Realize Empty.elim ![Ω, P, Q, p] ↔
      ∃ x : M, x.val ∈ Ω.val ∧ ∃ y : M, y.val ∈ Ω.val ∧ ∃ z : M, z.val ∈ Ω.val ∧
        p.val = pair (pair x.val y.val) z.val ∧ φ.Realize Empty.elim ![Ω, P, Q, x, y, z] := by
  have hp {n : ℕ} (q x y : Fin n) (xs : Fin n → M) :
      (orderedPairFormula q x y).Realize Empty.elim xs ↔
        (xs q).val = pair (xs x).val (xs y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q x y xs
  simp only [naturalBinaryGraphFormula, realize_boundedExists_model, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, hp, realize_reindex]
  have he (x y z r : M) :
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ![Ω, P, Q, p] x) y) z) r) ∘
        ![(0 : Fin 8), 1, 2, 4, 5, 6] = ![Ω, P, Q, x, y, z] := by
    funext i
    fin_cases i <;> rfl
  simp only [he]
  change (∃ x : M, x.val ∈ Ω.val ∧ ∃ y : M, y.val ∈ Ω.val ∧ ∃ z : M, z.val ∈ Ω.val ∧
    ∃ r : M, (r.val = pair x.val y.val ∧ p.val = pair r.val z.val) ∧
      φ.Realize Empty.elim ![Ω, P, Q, x, y, z]) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, r, ⟨hr, hp⟩, hφ⟩
    exact ⟨x, hx, y, hy, z, hz, hr ▸ hp, hφ⟩
  · rintro ⟨x, hx, y, hy, z, hz, hp, hφ⟩
    exact ⟨x, hx, y, hy, z, hz,
      ⟨pair x.val y.val, orderedPair_mem hM hpair x.property y.property⟩, ⟨rfl, hp⟩, hφ⟩

/-- Separation collects the whole graph of an internally recognized binary operation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    If a first-order formula recognizes $k=F(m,n)$ internally, Separation on
    $$(\omega\times\omega)\times\omega$$
    constructs $\Gamma_F\in M$. To expand the graph-membership formula, quantify $m,n,k\in\omega$, form the ordered
    pair $r=\langle m,n\rangle$, and require that the candidate pair be $\langle r,k\rangle$ and that the value formula
    hold. Pairing puts the intermediate set $r$ in $M$, and transitivity identifies all natural-number witnesses.
-/
theorem naturalBinaryGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence ψ)
    (φ : ForcingFormulas.Formula 6) (Ω P Q : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (f : ℕ → ℕ → ℕ)
    (hφ : ∀ x y z : M, ∀ i j k : ℕ,
      x.val = natOrdinal i → y.val = natOrdinal j → z.val = natOrdinal k →
      (φ.Realize Empty.elim ![Ω, P, Q, x, y, z] ↔ k = f i j)) :
    naturalBinaryGraph f ∈ M := by
  let D := ZFSet.prod (ZFSet.prod Ω.val Ω.val) Ω.val
  have hD : D ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property) Ω.property
  have hn (n : ℕ) : natOrdinal n ∈ Ω.val := hΩ.symm ▸ mem_omegaOrdinal.mpr ⟨n, rfl⟩
  have hnat (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (hn n) Ω.property
  have habs (p : M) : (naturalBinaryGraphFormula φ).Realize Empty.elim ![Ω, P, Q, p] ↔
      p.val ∈ naturalBinaryGraph f := by
    rw [realize_naturalBinaryGraphFormula hM hpair]
    constructor
    · rintro ⟨x, hx, y, hy, z, hz, hp, hψ⟩
      rw [hΩ] at hx hy hz
      obtain ⟨i, hi⟩ := mem_omegaOrdinal.mp hx
      obtain ⟨j, hj⟩ := mem_omegaOrdinal.mp hy
      obtain ⟨k, hk⟩ := mem_omegaOrdinal.mp hz
      have hf := (hφ x y z i j k hi.symm hj.symm hk.symm).mp hψ
      rw [hp, ← hi, ← hj, ← hk, pair_mem_naturalBinaryGraph, hf]
    · intro hp
      obtain ⟨⟨i, j⟩, hp⟩ := ZFSet.mem_range.mp hp
      exact ⟨⟨natOrdinal i, hnat i⟩, hn i, ⟨natOrdinal j, hnat j⟩, hn j,
        ⟨natOrdinal (f i j), hnat _⟩, hn _, hp.symm,
        (hφ _ _ _ i j (f i j) rfl rfl rfl).mpr rfl⟩
  have hsepD := separation_mem_of_absolute hM (naturalBinaryGraphFormula φ) (hsep _) ![Ω, P, Q] hD
    (fun p => p ∈ naturalBinaryGraph f) (by
      intro p _
      have he : Fin.snoc ![Ω, P, Q] p = ![Ω, P, Q, p] := by funext i; fin_cases i <;> rfl
      rw [he]
      exact habs p)
  have he : D.sep (fun p => p ∈ naturalBinaryGraph f) = naturalBinaryGraph f := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep]
    constructor
    · exact And.right
    · intro hp
      obtain ⟨⟨i, j⟩, rfl⟩ := ZFSet.mem_range.mp hp
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hn i, hn j⟩, hn _⟩,
        ZFSet.mem_range.mpr ⟨(i, j), rfl⟩⟩
  exact he ▸ hsepD

/-- The successor graph on omega. -/
def naturalSuccessorGraph : ZFSet.{u} := sequenceGraph (fun n => natOrdinal (n + 1))

def naturalSuccessorGraphPredicate : BoundedSetPredicate 2 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 1 2 3) (.successor 3 2)))

def naturalSuccessorGraphFormula : ForcingFormulas.Formula 2 := naturalSuccessorGraphPredicate.compile

lemma eval_naturalSuccessorGraphPredicate (p : ZFSet.{u}) :
    naturalSuccessorGraphPredicate.eval ![Ordinal.omega0.toZFSet, p] ↔ p ∈ naturalSuccessorGraph := by
  change (∃ x ∈ Ordinal.omega0.toZFSet, ∃ y ∈ Ordinal.omega0.toZFSet,
    p = pair x y ∧ y = insert x x) ↔ _
  constructor
  · rintro ⟨x, hx, y, _, hp, hy⟩
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx
    rw [← natOrdinal_succ] at hy
    rw [hp, hy]
    exact (pair_mem_sequenceGraph _ n _).mpr rfl
  · intro hp
    obtain ⟨n, he⟩ := ZFSet.mem_range.mp hp
    exact ⟨natOrdinal n, mem_omegaOrdinal.mpr ⟨n, rfl⟩,
      natOrdinal (n + 1), mem_omegaOrdinal.mpr ⟨n + 1, rfl⟩, he.symm, natOrdinal_succ n⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separation on $\omega\times\omega$ constructs the successor graph
    $$S:=\{\langle n,k\rangle:n,k\in\omega,\ k=n\cup\{n\}\}\in M.$$
-/
lemma naturalSuccessorGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (naturalSuccessorGraph : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  apply naturalSuccessorGraphPredicate.subset_mem hM (hsep _) ![Ω]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨n + 1, rfl⟩)).1
  intro p _
  exact eval_naturalSuccessorGraphPredicate p

/-- Addition is internally defined by iteration of successor. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal addition graph
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Its actual values are $n+1$. The iteration-recognition lemma gives
    $$M\models V(S,m,n,k)\quad\Longleftrightarrow\quad k=m+n.$$
    The graph construction above therefore gives $\Gamma_+\in M$.
-/
theorem naturalAdditionGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (naturalBinaryGraph (fun i j => i + j) : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let d : M := ⟨naturalSuccessorGraph, naturalSuccessorGraph_mem hM hinf hpair hunion hpower hsep⟩
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩) Ω.property⟩
  have hd : IsFunc Ω.val Ω.val d.val :=
    sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨n + 1, rfl⟩)
  have hfd (n : ℕ) : pair (natOrdinal n) (natOrdinal (Nat.succ n)) ∈ d.val :=
    (pair_mem_sequenceGraph _ n _).mpr rfl
  apply naturalBinaryGraph_mem hM hpair hunion hpower hsep numericIterationValueFormula Ω d z rfl
  intro x y w i j k hx hy hw
  simpa only [Nat.succ_iterate] using numericIterationValue_absolute hM hinf hpair hunion hpower hsep
    Ω d z x y w rfl rfl Nat.succ hd hfd i j k hx hy hw

end PolishSpaceBook.SetTheoryModels
