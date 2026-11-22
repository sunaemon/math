module

public import PolishSpaceBook.BorelSetCodeFormulas

@[expose] public section


/-! # Constructing the parameters of internal Borel truth from input graphs -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    The nonzero-label predicate and the live-child relation are
    $$\begin{aligned}
    A(s)&:\equiv\exists a\in\omega\;(\langle s,a\rangle\in\ell\land a\ne0),\\
    R&:=\{\langle t,s\rangle\in T\times T:J(t,s)\land A(t)\land A(s)\}.
    \end{aligned}$$
-/
def childRelation (l : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod finiteSequences finiteSequences).sep
    (fun q => ∃ t ∈ finiteSequences, ∃ s ∈ finiteSequences, q = pair t s ∧ LiveChild l t s)

lemma pair_mem_childRelation (c : BorelExpression) (t s : List ℕ) :
    pair (wordGraph t) (wordGraph s) ∈ childRelation (c.labelGraph : ZFSet.{u}) ↔ c.Child t s := by
  rw [childRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, _, b, _, he, h⟩
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp he
    rw [← ha, ← hb] at h
    exact (liveChild_labelGraph c t s).mp h
  · intro h
    have ht : wordGraph t ∈ (finiteSequences : ZFSet.{u}) := mem_finiteSequences.mpr ⟨t, rfl⟩
    have hs : wordGraph s ∈ (finiteSequences : ZFSet.{u}) := mem_finiteSequences.mpr ⟨s, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨ht, hs⟩,
      wordGraph t, ht, wordGraph s, hs, rfl, (liveChild_labelGraph c t s).mpr h⟩

/-- Ω,T,l,zero are parameters, followed by the candidate ordered pair. -/
def childRelationPredicate : BoundedSetPredicate 5 :=
  .ex 1 (.ex 1 (.conj (.orderedPair (4 : Fin 7) 5 6) (liveChildPredicate 0 2 3 5 6)))

def childRelationFormula : ForcingFormulas.Formula 5 := childRelationPredicate.compile

lemma realize_childRelationFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω T l z q : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hz : z.val = natOrdinal 0) :
    childRelationFormula.Realize Empty.elim ![Ω, T, l, z, q] ↔
      ∃ t ∈ T.val, ∃ s ∈ T.val, q.val = pair t s ∧ LiveChild l.val t s := by
  rw [childRelationFormula, BoundedSetPredicate.realize_compile hM]
  simp [childRelationPredicate, liveChildPredicate, immediateWordPredicate, liveLabelPredicate,
    BoundedSetPredicate.eval, hΩ, hz, LiveChild, ImmediateWordExtension, Fin.snoc, Fin.castPred, Fin.castLT]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    These sets belong to $M$ by Separation. The graph equations identify their external interpretations with
    the child relation, union labels, and complement labels of the given expression.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put
    $$R_\ell:=\{\langle t,s\rangle\in T\times T:
    J(t,s)\land\ell(t)\ne0\land\ell(s)\ne0\}.$$
    The relation graph belongs to $M$ when $\ell\in M$. Let $W(T,R)$ be the internal subset-minimum formula
    of §{sec:internal-rank-existence}: every nonempty subset of $T$ belonging to the model has an $R$-minimal
    member. Define a first-order formula $\Phi(\ell)$ by requiring that $\ell:T\to\omega$, that $L(\ell)$ holds,
    and that there exists a relation graph $R=R_\ell$ satisfying $W(T,R)$.
    The relation equation is bounded, using a subset of $T\times T$ and tests on all pairs of nodes.
    The well-foundedness clause uses the subset-minimum formula; we do not regard it as a local bounded test.
-/
theorem childRelation_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {l : ZFSet.{u}} (hl : l ∈ M) : childRelation l ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let T : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let z : M := ⟨natOrdinal 0, natOrdinal_zero.symm ▸ empty_mem_of_infinity hM hinf⟩
  have hB := prod_mem_of_separation hM hpair hunion hpower (hsep _) T.property T.property
  apply separation_mem_of_absolute hM childRelationFormula (hsep _) ![Ω, T, ⟨l, hl⟩, z] hB
  intro q _
  have he : Fin.snoc ![Ω, T, ⟨l, hl⟩, z] q = ![Ω, T, ⟨l, hl⟩, z, q] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact realize_childRelationFormula hM Ω T ⟨l, hl⟩ z q rfl rfl

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    These sets belong to $M$ by Separation. The graph equations identify their external interpretations with
    the child relation, union labels, and complement labels of the given expression.
-/
theorem labelSlice_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hT : (finiteSequences : ZFSet.{u}) ∈ M) {l a : ZFSet.{u}} (hl : l ∈ M) (ha : a ∈ M) :
    labelSlice l a ∈ M := by
  apply separation_mem_of_absolute hM (pairMemberFormula (0 : Fin 3) 2 1) (hsep _)
    ![⟨l, hl⟩, ⟨a, ha⟩] hT
  intro s _
  exact realize_pairMemberFormula_model hM _ _ _ _

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Consequently form
    $$\begin{aligned}
    L:=\{s\in T:\exists n,m\in\omega\;[&m=n+3\land\langle s,m\rangle\in\ell\\
    &{}\land\exists w\in T\;(\langle n,w\rangle\in B\land w\IncludedIn g)]\}.
    \end{aligned}$$
-/
def trueLeaves (l b x : ZFSet.{u}) : ZFSet.{u} := finiteSequences.sep (TrueLeaf l b x)

lemma mem_trueLeaves (c : BorelExpression) (b : ℕ → List ℕ) (x : ℕ → ℕ) (s : List ℕ) :
    wordGraph s ∈ trueLeaves c.labelGraph (basisWordGraph b) (pointGraph x) ↔
      3 ≤ c s ∧ x ∈ cyl (b (c s - 3)) := by
  rw [trueLeaves, ZFSet.mem_sep, trueLeaf_labelGraph]
  exact ⟨And.right, fun h => ⟨mem_finiteSequences.mpr ⟨s, rfl⟩, h⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separation gives $L\in M$. By the input graph equations, these are exactly the leaf nodes
    whose cylinders contain the fixed point.
-/
theorem trueLeaves_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hT : (finiteSequences : ZFSet.{u}) ∈ M) {l b x : ZFSet.{u}}
    (hl : l ∈ M) (hb : b ∈ M) (hx : x ∈ M) : trueLeaves l b x ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let T : M := ⟨_, hT⟩
  apply separation_mem_of_absolute hM (trueLeafFormula (0 : Fin 6) 1 2 3 4 5) (hsep _)
    ![Ω, T, ⟨l, hl⟩, ⟨b, hb⟩, ⟨x, hx⟩] hT
  intro s _
  exact realize_trueLeafFormula hM hpair hunion _ _ _ _ _ _ _ rfl rfl

/-- No node-relation or leaf-truth-set closure is left as an extra premise. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The preceding constructions put $T,R,U,C,L$ in $M$ using just the stated axioms and input graphs.
    The correspondence $s\mapsto e(s)$ is a bijection and identifies the live-child relations, so it transfers
    external well-foundedness. The comparison theorem in §{sec:internal-borel-evaluations} now applies and
    puts the actual external truth set in $M$. Its nodewise equations give the displayed equivalence.
-/
theorem codedTruth_mem_of_graphs {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (x : ℕ → ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) (hx : pointGraph x ∈ M) :
    c.codedTruth hw (fun n => cyl (b n)) x wordEquiv ∈ M := by
  have hT := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  exact c.codedTruth_mem hM hpair hunion hsep hw (fun n => cyl (b n)) x
    ⟨_, hT⟩ ⟨_, childRelation_mem hM hinf hpair hunion hpower hsep hc⟩
    ⟨_, labelSlice_mem hM hsep hT hc (hn 1)⟩ ⟨_, labelSlice_mem hM hsep hT hc (hn 2)⟩
    ⟨_, trueLeaves_mem hM hinf hpair hunion hsep hT hc hb hx⟩ wordEquiv
    (pair_mem_childRelation c) (fun s => mem_labelSlice c s 1) (fun s => mem_labelSlice c s 2)
    (mem_trueLeaves c b x)

/-- The internal truth set agrees at all nodes, including the root. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal evaluation of cylinder codes
-/
theorem exists_internal_cylinder_evaluation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (x : ℕ → ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) (hx : pointGraph x ∈ M) :
    ∃ E : M, ∀ s : List ℕ, wordGraph s ∈ E.val ↔ x ∈ c.evaluate hw (fun n => cyl (b n)) s := by
  refine ⟨⟨_, c.codedTruth_mem_of_graphs hM hinf hpair hunion hpower hsep hw b x hc hb hx⟩, ?_⟩
  intro s
  exact c.mem_codedTruth hw (fun n => cyl (b n)) x wordEquiv s

end PolishSpaceBook.BorelExpression
