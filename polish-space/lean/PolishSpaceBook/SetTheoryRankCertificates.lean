module

public import PolishSpaceBook.SetTheoryOrdinalIsoFormulas
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section


/-! # Absolute recognition of ordinal-valued rank certificates

The graph and an ordinal bound are supplied as model elements. Recognition is
bounded and rules out external descending chains without assuming external
well-foundedness. Existence of an internal certificate is a separate obligation.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters W,R,α,f; the four quantified variables are x,y,b,c. -/
def rankComparisonPredicate : BoundedSetPredicate 4 :=
  .all 0 (.all 0 (.all 2 (.all 2
    (.disj (.neg (.conj (.conj (.pairMember (1 : Fin 8) 4 5) (.pairMember 3 4 6))
      (.pairMember 3 5 7))) (.member 6 7)))))

def rankComparisonFormula : ForcingFormulas.Formula 4 := rankComparisonPredicate.compile

lemma rankComparisonFormula_deltaZero : IsDeltaZero rankComparisonFormula :=
  rankComparisonPredicate.compile_deltaZero

/-- The function need not be injective, onto, or the least possible rank. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    A rank can be transferred as a fixed function graph with an ordinal bound. For sets $W,R,\alpha,f$, define
    $$\begin{aligned}
    \kappa(W,R,\alpha,f)\;:\equiv\;&\mathrm{Ord}(\alpha)\land(f:W\to\alpha)\\
    &{}\land\forall x,y\in W\,\forall\beta,\gamma\in\alpha\\
    &\quad\bigl[(\langle x,y\rangle\in R\land\langle x,\beta\rangle\in f\\
    &\qquad{}\land\langle y,\gamma\rangle\in f)\longrightarrow\beta\in\gamma\bigr].
    \end{aligned}$$
    We orient $R$ from a smaller rank to a larger rank. The graph $f$ need not be injective or onto, and its values need
    not be the least possible ranks. The ordinal, function, and pair predicates have the bounded expansions given in
    §{sec:zfc-absoluteness}; every remaining quantifier is bounded by $W$ or $\alpha$. Thus $\kappa$ is
    a $\Delta_0$ formula.
-/
def rankCertificateFormula : ForcingFormulas.Formula 4 :=
  ordinalFormula 2 ⊓ functionFormula 0 2 3 ⊓ rankComparisonFormula

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    A rank can be transferred as a fixed function graph with an ordinal bound. For sets $W,R,\alpha,f$, define
    $$\begin{aligned}
    \kappa(W,R,\alpha,f)\;:\equiv\;&\mathrm{Ord}(\alpha)\land(f:W\to\alpha)\\
    &{}\land\forall x,y\in W\,\forall\beta,\gamma\in\alpha\\
    &\quad\bigl[(\langle x,y\rangle\in R\land\langle x,\beta\rangle\in f\\
    &\qquad{}\land\langle y,\gamma\rangle\in f)\longrightarrow\beta\in\gamma\bigr].
    \end{aligned}$$
    We orient $R$ from a smaller rank to a larger rank. The graph $f$ need not be injective or onto, and its values need
    not be the least possible ranks. The ordinal, function, and pair predicates have the bounded expansions given in
    §{sec:zfc-absoluteness}; every remaining quantifier is bounded by $W$ or $\alpha$. Thus $\kappa$ is
    a $\Delta_0$ formula.
-/
lemma rankCertificateFormula_deltaZero : IsDeltaZero rankCertificateFormula :=
  ((ordinalFormula_deltaZero _).and (functionFormula_deltaZero _ _ _)).and
    rankComparisonFormula_deltaZero

/-- External graph conditions expressed by the bounded certificate formula. -/
def IsRankCertificate (W R α f : ZFSet.{u}) : Prop :=
  α.IsOrdinal ∧ IsFunc W α f ∧
    ∀ x ∈ W, ∀ y ∈ W, ∀ b ∈ α, ∀ c ∈ α,
      pair x y ∈ R → pair x b ∈ f → pair y c ∈ f → b ∈ c

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The bounded ordinal and function predicates have their actual meanings in a transitive domain. Every member of
    $W$ or $\alpha$ belongs to $M$, so the four bounded quantifiers range over all actual candidates. The ordered-pair
    predicates recognize the same pairs and the same graph entries. Consequently the last clause says exactly that
    the actual values at $R$-related arguments satisfy the displayed membership relation.
    The argument also proves the converse.
-/
lemma realize_rankComparisonFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (W R α f : M) :
    rankComparisonFormula.Realize Empty.elim ![W, R, α, f] ↔
      ∀ x ∈ W.val, ∀ y ∈ W.val, ∀ b ∈ α.val, ∀ c ∈ α.val,
        pair x y ∈ R.val → pair x b ∈ f.val → pair y c ∈ f.val → b ∈ c := by
  rw [rankComparisonFormula, BoundedSetPredicate.realize_compile hM]
  simp [rankComparisonPredicate, BoundedSetPredicate.eval, Fin.snoc, Fin.castPred, Fin.castLT,
    or_iff_not_imp_left, and_imp]

/-- Internal recognition agrees with the actual function graph and ordinal comparison. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal recognition of rank certificates
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The bounded ordinal and function predicates have their actual meanings in a transitive domain. Every member of
    $W$ or $\alpha$ belongs to $M$, so the four bounded quantifiers range over all actual candidates. The ordered-pair
    predicates recognize the same pairs and the same graph entries. Consequently the last clause says exactly that
    the actual values at $R$-related arguments satisfy the displayed membership relation.
    The argument also proves the converse.
-/
theorem realize_rankCertificateFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (W R α f : M) :
    rankCertificateFormula.Realize Empty.elim ![W, R, α, f] ↔
      IsRankCertificate W.val R.val α.val f.val := by
  have ho : (ordinalFormula (2 : Fin 4)).Realize Empty.elim ![W, R, α, f] ↔ α.val.IsOrdinal :=
    realize_ordinalFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) 2 ![W, R, α, f]
  have hf : (functionFormula (0 : Fin 4) 2 3).Realize Empty.elim ![W, R, α, f] ↔
      IsFunc W.val α.val f.val :=
    realize_functionFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) 0 2 3 ![W, R, α, f]
  simp only [rankCertificateFormula, BoundedFormula.realize_inf, ho, hf,
    realize_rankComparisonFormula hM, IsRankCertificate, and_assoc]

/-- Transfer the same graph, not a newly selected rank. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Transfer of a fixed rank certificate
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Apply the recognition lemma in both domains. Both sides express the same external condition on the same graph.
-/
theorem rankCertificate_absolute {M N : ZFSet.{u}} (hM : M.IsTransitive) (hN : N.IsTransitive)
    (hMN : M ⊆ N) (W R α f : M) :
    rankCertificateFormula.Realize Empty.elim ![W, R, α, f] ↔
      rankCertificateFormula.Realize Empty.elim
        ![(⟨W.val, hMN W.property⟩ : N), ⟨R.val, hMN R.property⟩,
          ⟨α.val, hMN α.property⟩, ⟨f.val, hMN f.property⟩] := by
  rw [realize_rankCertificateFormula hM, realize_rankCertificateFormula hN]

/-- Foundation applied to the values excludes every external descending chain. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    If an external descending sequence existed, applying $f$ to its entries would give a sequence of ordinal values
    with each value a member of its predecessor. Foundation rules this out. Equivalently, pull back the well-founded
    membership relation along $f$ and use that every $R$-step is a step in that pullback.
-/
theorem IsRankCertificate.wellFounded {W R α f : ZFSet.{u}}
    (h : IsRankCertificate W R α f) :
    WellFounded (fun x y : W => pair x.val y.val ∈ R) := by
  let g : W → α := fun x =>
    ⟨Classical.choose (h.2.1.2 x.val x.property),
      (pair_mem_prod.mp (h.2.1.1 (Classical.choose_spec (h.2.1.2 x.val x.property)).1)).2⟩
  have hg (x : W) : pair x.val (g x).val ∈ f :=
    (Classical.choose_spec (h.2.1.2 x.val x.property)).1
  apply (InvImage.wf (fun x : W => (g x).val) ZFSet.mem_wf).mono
  intro x y hxy
  exact h.2.2 x.val x.property y.val y.property (g x).val (g x).property
    (g y).val (g y).property hxy (hg x) (hg y)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Transfer of a fixed rank certificate
-/
theorem wellFounded_of_internal_rank {M : ZFSet.{u}} (hM : M.IsTransitive) (W R α f : M)
    (hr : rankCertificateFormula.Realize Empty.elim ![W, R, α, f]) :
    WellFounded (fun x y : W.val => pair x.val y.val ∈ R.val) :=
  ((realize_rankCertificateFormula hM W R α f).mp hr).wellFounded

end PolishSpaceBook.SetTheoryModels
