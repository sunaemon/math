module

public import PolishSpaceBook.SetTheoryNaturalGraphs

@[expose] public section

/-! # Internal multiplication by iteration of addition -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- A graph on ordered-pair inputs, evaluated at two specified arguments. -/
def binaryValueFormula {n : ℕ} (G x y z : Fin n) : ForcingFormulas.Formula n :=
  (orderedPairFormula (Fin.last n) x.castSucc y.castSucc ⊓
    pairMemberFormula G.castSucc (Fin.last n) z.castSucc).ex

lemma realize_binaryValueFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) {n : ℕ} (G x y z : Fin n) (xs : Fin n → M) :
    (binaryValueFormula G x y z).Realize Empty.elim xs ↔
      pair (pair (xs x).val (xs y).val) (xs z).val ∈ (xs G).val := by
  have hp {n : ℕ} (q x y : Fin n) (ys : Fin n → M) :
      (orderedPairFormula q x y).Realize Empty.elim ys ↔
        (ys q).val = pair (ys x).val (ys y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q x y ys
  simp only [binaryValueFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    hp, realize_pairMemberFormula_model hM, Fin.snoc_last, Fin.snoc_castSucc]
  exact ⟨fun ⟨r, hr, h⟩ => hr ▸ h,
    fun h => ⟨⟨_, orderedPair_mem hM hpair (xs x).property (xs y).property⟩, rfl, h⟩⟩

/-- Parameters omega, binary graph, fixed right argument, candidate ordered pair. -/
def naturalRightSectionMemberPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 3 4 5) (binaryMemberAt 1 4 2 5)))

def naturalRightSectionMemberFormula : ForcingFormulas.Formula 4 :=
  naturalRightSectionMemberPredicate.compile

lemma eval_naturalRightSectionMemberPredicate (f : ℕ → ℕ → ℕ) (m : ℕ) (p : ZFSet.{u}) :
    naturalRightSectionMemberPredicate.eval
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph f, natOrdinal m, p] ↔
      p ∈ sequenceGraph (fun n => natOrdinal (f n m)) := by
  simp only [naturalRightSectionMemberPredicate, BoundedSetPredicate.eval,
    eval_binaryMemberAt, Fin.snoc, Fin.castLT]
  change (∃ x ∈ Ordinal.omega0.toZFSet, ∃ y ∈ Ordinal.omega0.toZFSet,
    p = pair x y ∧ pair (pair x (natOrdinal m)) y ∈ naturalBinaryGraph f) ↔ _
  constructor
  · rintro ⟨x, hx, y, _, hp, hxy⟩
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx
    rw [pair_mem_naturalBinaryGraph] at hxy
    rw [hp, hxy]
    exact (pair_mem_sequenceGraph _ n _).mpr rfl
  · intro hp
    obtain ⟨n, he⟩ := ZFSet.mem_range.mp hp
    exact ⟨natOrdinal n, mem_omegaOrdinal.mpr ⟨n, rfl⟩,
      natOrdinal (f n m), mem_omegaOrdinal.mpr ⟨f n m, rfl⟩, he.symm,
      (pair_mem_naturalBinaryGraph f n m _).mpr rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For each $m\in\omega$, separate the section
    $$d_m:=\{\langle x,y\rangle\in\omega\times\omega:
    \langle\langle x,m\rangle,y\rangle\in\Gamma_+\}.$$
-/
lemma naturalRightSection_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (f : ℕ → ℕ → ℕ) (hG : naturalBinaryGraph f ∈ M) (m : ℕ) :
    sequenceGraph (fun n => natOrdinal (f n m)) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let G : M := ⟨naturalBinaryGraph f, hG⟩
  let a : M := ⟨natOrdinal m, hM.mem_trans (mem_omegaOrdinal.mpr ⟨m, rfl⟩) Ω.property⟩
  apply naturalRightSectionMemberPredicate.subset_mem hM (hsep _) ![Ω, G, a]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨f n m, rfl⟩)).1
  intro p _
  have he : Fin.snoc (Subtype.val ∘ ![Ω, G, a]) p =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph f, natOrdinal m, p] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact eval_naturalRightSectionMemberPredicate f m p

/-- Recognize the entire right section by its function type and values. -/
def naturalRightSectionPredicate : BoundedSetPredicate 4 :=
  .conj (.function 0 0 3) (.all 0 (.all 0
    (.iff (.pairMember 3 4 5) (binaryMemberAt 1 4 2 5))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    To express this uniformly in $m$, let $D(A,m,d)$ assert that $d:\omega\to\omega$ and
    $$\forall x,y\in\omega\;
    \bigl(\langle x,y\rangle\in d\longleftrightarrow
    \langle\langle x,m\rangle,y\rangle\in A\bigr).$$
-/
def naturalRightSectionFormula : ForcingFormulas.Formula 4 := naturalRightSectionPredicate.compile

lemma realize_naturalRightSectionFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω G a d : M) :
    naturalRightSectionFormula.Realize Empty.elim ![Ω, G, a, d] ↔
      IsFunc Ω.val Ω.val d.val ∧ ∀ x ∈ Ω.val, ∀ y ∈ Ω.val,
        (pair x y ∈ d.val ↔ pair (pair x a.val) y ∈ G.val) := by
  simpa [naturalRightSectionFormula, naturalRightSectionPredicate, BoundedSetPredicate.eval,
    eval_binaryMemberAt, Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT] using
    naturalRightSectionPredicate.realize_compile hM ![Ω, G, a, d]

/-- Parameters omega, addition graph, zero, m,n,k. -/
def naturalMultiplicationFormula : ForcingFormulas.Formula 6 :=
  (reindex naturalRightSectionFormula ![(0 : Fin 7), 1, 3, 6] ⊓
    reindex numericIterationValueFormula ![(0 : Fin 7), 6, 2, 2, 4, 5]).ex

lemma realize_naturalMultiplicationFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω A z a n y : M) :
    naturalMultiplicationFormula.Realize Empty.elim ![Ω, A, z, a, n, y] ↔
      ∃ d : M, (IsFunc Ω.val Ω.val d.val ∧ ∀ x ∈ Ω.val, ∀ y ∈ Ω.val,
        (pair x y ∈ d.val ↔ pair (pair x a.val) y ∈ A.val)) ∧
        numericIterationValueFormula.Realize Empty.elim ![Ω, d, z, z, n, y] := by
  simp only [naturalMultiplicationFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex]
  have he (d : M) : Fin.snoc ![Ω, A, z, a, n, y] d ∘ ![(0 : Fin 7), 1, 3, 6] = ![Ω, A, a, d] := by
    funext i; fin_cases i <;> rfl
  have he' (d : M) : Fin.snoc ![Ω, A, z, a, n, y] d ∘ ![(0 : Fin 7), 6, 2, 2, 4, 5] =
      ![Ω, d, z, z, n, y] := by funext i; fin_cases i <;> rfl
  simp only [he, he', realize_naturalRightSectionFormula hM]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    This belongs to $M$ and is the graph of $x\mapsto x+m$. Induction on $n$ shows that its iteration from $0$ has
    value $mn$:
    $$\begin{aligned}
    d_m^0(0)&=0=m\cdot0,\\
    d_m^{n+1}(0)&=d_m^n(0)+m=mn+m=m(n+1).
    \end{aligned}$$
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Then
    $$M\models\exists d\;\bigl(D(\Gamma_+,m,d)\land V(d,0,n,k)\bigr)
    \quad\Longleftrightarrow\quad k=mn.$$
    In the forward direction, the section clause fixes every next value and induction gives the product. In the
    reverse direction, the internally constructed section supplies the witness.
-/
lemma naturalMultiplication_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (Ω A z a n y : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hA : A.val = naturalBinaryGraph (fun i j => i + j)) (hz : z.val = natOrdinal 0)
    (i j k : ℕ) (ha : a.val = natOrdinal i) (hn : n.val = natOrdinal j) (hy : y.val = natOrdinal k) :
    naturalMultiplicationFormula.Realize Empty.elim ![Ω, A, z, a, n, y] ↔ k = i * j := by
  rw [realize_naturalMultiplicationFormula hM]
  have homega (n : ℕ) : natOrdinal n ∈ Ω.val := hΩ.symm ▸ mem_omegaOrdinal.mpr ⟨n, rfl⟩
  have hiter (n : ℕ) : (fun t => t + i)^[n] 0 = i * n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, Nat.mul_succ]
  constructor
  · rintro ⟨d, ⟨hd, hsection⟩, hval⟩
    have hfd (t : ℕ) : pair (natOrdinal t) (natOrdinal (t + i)) ∈ d.val := by
      apply (hsection _ (homega t) _ (homega _)).mpr
      rw [hA, ha, pair_mem_naturalBinaryGraph]
    have hv := (numericIterationValue_absolute hM hinf hpair hunion hpower hsep Ω d z z n y hΩ hz
      (fun t => t + i) hd hfd 0 j k hz hn hy).mp hval
    exact hv.trans (hiter j)
  · intro hk
    let d : M := ⟨sequenceGraph (fun t => natOrdinal (t + i)),
      naturalRightSection_mem hM hinf hpair hunion hpower hsep (fun t i => t + i) (hA ▸ A.property) i⟩
    have hd : IsFunc Ω.val Ω.val d.val := by
      rw [hΩ]
      exact sequenceGraph_isFunc _ (fun t => mem_omegaOrdinal.mpr ⟨t + i, rfl⟩)
    have hfd (t : ℕ) : pair (natOrdinal t) (natOrdinal (t + i)) ∈ d.val :=
      (pair_mem_sequenceGraph _ t _).mpr rfl
    refine ⟨d, ⟨hd, ?_⟩, ?_⟩
    · intro x hx y _
      rw [hΩ] at hx
      obtain ⟨t, rfl⟩ := mem_omegaOrdinal.mp hx
      rw [hA, ha, pair_mem_naturalBinaryGraph]
      exact pair_mem_sequenceGraph _ t y
    · apply (numericIterationValue_absolute hM hinf hpair hunion hpower hsep Ω d z z n y hΩ hz
        (fun t => t + i) hd hfd 0 j k hz hn hy).mpr
      exact hk.trans (hiter j).symm

/-- The multiplication graph belongs to the model, not just each finite product. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal multiplication graph
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separation now collects
    $\Gamma_\times$.
-/
theorem naturalMultiplicationGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (naturalBinaryGraph (fun i j => i * j) : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let A : M := ⟨naturalBinaryGraph (fun i j => i + j), naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩) Ω.property⟩
  apply naturalBinaryGraph_mem hM hpair hunion hpower hsep naturalMultiplicationFormula Ω A z rfl
  intro x y w i j k hx hy hw
  exact naturalMultiplication_absolute hM hinf hpair hunion hpower hsep
    Ω A z x y w rfl rfl rfl i j k hx hy hw

end PolishSpaceBook.SetTheoryModels
