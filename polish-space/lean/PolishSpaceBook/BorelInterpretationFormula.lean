module

public import PolishSpaceBook.BorelPointGraphs

@[expose] public section

/-! # A uniform first-order formula for set-coded Borel membership -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
open SetTheoryModels.BooleanEvaluation
universe u

private lemma realize_all (M : ZFSet.{u}) {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : M, y.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs y) :=
  realize_boundedAll (M : ZFClass) i φ xs

/-- The leaf set is uniquely specified by bounded membership tests. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Write $\lambda(\ell,B,g,t)$ for the leaf predicate defining $L$ in §{sec:internal-borel-inputs}.
    Specify its entire truth set by the first-order formula
    $$\begin{aligned}
    \chi(\ell,B,g,L)\;:\equiv\;&L\IncludedIn T\\
    &{}\land\forall t\in T\;
    (t\in L\longleftrightarrow\lambda(\ell,B,g,t)).
    \end{aligned}$$
    The parameters $\omega,T$ are suppressed.
-/
def leafSetFormula {n : ℕ} (Ω T l b g L : Fin n) : ForcingFormulas.Formula n :=
  orderSubsetFormula L T ⊓ boundedAll T
    ((memberAt (Fin.last n) L.castSucc).iff
      (trueLeafFormula Ω.castSucc T.castSucc l.castSucc b.castSucc g.castSucc (Fin.last n)))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For $g,L\in M$, this formula holds internally exactly when
    $L$ is the actual leaf-truth set associated with $g$.
    Indeed, transitivity makes the bounded quantifier range over every actual member of $T$, and the preceding
    leaf calculation identifies the membership test. The subset clause excludes all other elements.
-/
lemma realize_leafSetFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {n : ℕ} (Ω T l b g L : Fin n) (xs : Fin n → M)
    (hΩ : (xs Ω).val = Ordinal.omega0.toZFSet) (hT : (xs T).val = finiteSequences) :
    (leafSetFormula Ω T l b g L).Realize Empty.elim xs ↔
      (xs L).val = trueLeaves (xs l).val (xs b).val (xs g).val := by
  have hf (s : M) :
      (trueLeafFormula Ω.castSucc T.castSucc l.castSucc b.castSucc g.castSucc (Fin.last n)).Realize
        Empty.elim (Fin.snoc xs s) ↔ TrueLeaf (xs l).val (xs b).val (xs g).val s.val := by
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
      (realize_trueLeafFormula hM hpair hunion Ω.castSucc T.castSucc l.castSucc b.castSucc
      g.castSucc (Fin.last n) (Fin.snoc xs s)
      (by simpa only [Fin.snoc_castSucc] using hΩ)
      (by simpa only [Fin.snoc_castSucc] using hT))
  simp only [leafSetFormula, BoundedFormula.realize_inf, realize_orderSubsetFormula hM,
    realize_all, BoundedFormula.realize_iff,
    realize_memberAt_model, Fin.snoc_last, Fin.snoc_castSucc, hf, hT]
  constructor
  · rintro ⟨hsub, h⟩
    apply ZFSet.ext
    intro s
    rw [trueLeaves, ZFSet.mem_sep]
    constructor
    · intro hs
      have ht := hsub hs
      exact ⟨ht, (h ⟨s, hM.mem_trans ht (hT ▸ (xs T).property)⟩ ht).mp hs⟩
    · rintro ⟨ht, hs⟩
      exact (h ⟨s, hM.mem_trans ht (hT ▸ (xs T).property)⟩ ht).mpr hs
  · intro he
    constructor
    · intro s hs
      exact (ZFSet.mem_sep.mp (he ▸ hs)).1
    · intro s hs
      rw [he, trueLeaves, ZFSet.mem_sep]
      exact and_iff_right hs

/-- Parameters Ω,T,R,U,C,l,b,s, followed by the candidate point graph g. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Now let $\sigma_L$ denote the partial-evaluation formula of §{sec:internal-borel-evaluations} with leaf parameter $L$.
    Define
    $$\begin{aligned}
    \Phi(\ell,B,t,g)\;:\equiv\;\exists L\,\exists E\;
    \bigl(&\chi(\ell,B,g,L)\\
    &{}\land\sigma_L(T,E)\land t\in E\bigr).
    \end{aligned}$$
    Here $\omega,T,R,U,C$ are additional fixed parameters. This is one formula for all points and nodes;
    it contains no external evaluation as a parameter.
-/
def interpretationFormula : ForcingFormulas.Formula 9 :=
  (leafSetFormula (0 : Fin 11) 1 5 6 8 9 ⊓
    (partialFormula 1 2 3 4 9 1 10 ⊓ memberAt 7 10)).ex.ex

lemma realize_interpretationFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (Ω T R U C l b s g : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hT : T.val = finiteSequences) :
    interpretationFormula.Realize Empty.elim ![Ω, T, R, U, C, l, b, s, g] ↔
      ∃ L E : M, L.val = trueLeaves l.val b.val g.val ∧
        Partial T.val R.val U.val C.val L.val T.val E.val ∧ s.val ∈ E.val := by
  have hl (L E : M) :
      (leafSetFormula (0 : Fin 11) 1 5 6 8 9).Realize Empty.elim
        (Fin.snoc (Fin.snoc ![Ω, T, R, U, C, l, b, s, g] L) E) ↔
          L.val = trueLeaves l.val b.val g.val :=
    realize_leafSetFormula hM hpair hunion _ _ _ _ _ _ _ hΩ hT
  simp only [interpretationFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    hl, realize_partialFormula hM, realize_memberAt_model]
  rfl

/-- The same first-order formula works for every old point and every node. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Fix $g_x\in X_M$. The leaf construction gives its actual set $L\in M$, and the internal-evaluation theorem
    gives the actual truth set $E\in M$. These witness $\Phi(\ell,B,e(s),g_x)$ whenever $x\in A_s$.
    Conversely, any internal witnesses must use that same leaf set by $\chi$; bounded absoluteness makes the
    second witness a complete actual evaluation. Uniqueness of evaluations then gives $e(s)\in E$ exactly when
    $x\in A_s$.
-/
theorem realize_interpretationFormula_graphs {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (x : ℕ → ℕ)
    (Ω T R U C l B s g : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hR : R.val = childRelation c.labelGraph)
    (hU : U.val = labelSlice c.labelGraph (natOrdinal 1))
    (hC : C.val = labelSlice c.labelGraph (natOrdinal 2))
    (hl : l.val = c.labelGraph) (hB : B.val = basisWordGraph b)
    (w : List ℕ) (hs : s.val = wordGraph w) (hg : g.val = pointGraph x) :
    interpretationFormula.Realize Empty.elim ![Ω, T, R, U, C, l, B, s, g] ↔
      x ∈ c.evaluate hw (fun n => cyl (b n)) w := by
  rw [realize_interpretationFormula hM hpair hunion _ _ _ _ _ _ _ _ _ hΩ hT]
  have hTmem : (finiteSequences : ZFSet.{u}) ∈ M := hT ▸ T.property
  have hLmem := trueLeaves_mem hM hinf hpair hunion hsep hTmem
    (hl ▸ l.property) (hB ▸ B.property) (hg ▸ g.property)
  let E := c.codedTruth hw (fun n => cyl (b n)) x wordEquiv.{u}
  have hE := c.codedTruth_partial hw (fun n => cyl (b n)) x wordEquiv.{u}
    (pair_mem_childRelation c) (fun s => mem_labelSlice c s 1) (fun s => mem_labelSlice c s 2)
    (mem_trueLeaves c b x)
  have hEmem : E ∈ M := c.codedTruth_mem_of_graphs hM hinf hpair hunion hpower hsep hw b x
    (hl ▸ l.property) (hB ▸ B.property) (hg ▸ g.property)
  have hwell : WellFounded (fun t s : (finiteSequences : ZFSet.{u}) =>
      pair t.val s.val ∈ childRelation c.labelGraph) := by
    apply (InvImage.wf wordEquiv.{u}.symm hw).mono
    intro t s hts
    exact (pair_mem_childRelation c (wordEquiv.{u}.symm t) (wordEquiv.{u}.symm s)).mp (by
      change pair (wordEquiv.{u} (wordEquiv.{u}.symm t)).val (wordEquiv.{u} (wordEquiv.{u}.symm s)).val ∈ _
      simpa only [Equiv.apply_symm_apply] using hts)
  constructor
  · rintro ⟨L, F, hL, hF, hsw⟩
    rw [hl, hB, hg] at hL
    rw [hT, hR, hU, hC, hL] at hF
    have he : F.val = E := hF.unique hwell hE
    have hwe : wordGraph w ∈ E := hs ▸ (he ▸ hsw)
    exact (c.mem_codedTruth hw (fun n => cyl (b n)) x wordEquiv.{u} w).mp hwe
  · intro hx
    refine ⟨⟨_, hLmem⟩, ⟨E, hEmem⟩, ?_, ?_, ?_⟩
    · simp only [hl, hB, hg]
    · simpa only [hT, hR, hU, hC] using hE
    · rw [hs]
      exact (c.mem_codedTruth hw (fun n => cyl (b n)) x wordEquiv.{u} w).mpr hx

end PolishSpaceBook.BorelExpression
