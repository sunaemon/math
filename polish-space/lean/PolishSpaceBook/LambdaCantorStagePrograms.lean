module

public import PolishSpaceBook.LambdaRankMatrix
public import PolishSpaceBook.LambdaCantorDerivativeCompiler
public import PolishSpaceBook.LambdaTemplateIndices

@[expose] public section

/-! # Guarded lambda programs for a Cantor--Bendixson stage

The lower program index is computed by a self-indexed family and transformed
by the derivative compiler. Only genuine predecessors trigger evaluation.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaRelative RankBound
namespace CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def derivativeEvalProgram (D : AlphaTerm) := relativeComposeProgram uniformInterpreterProgram
  (pairOutputProgram (mapOutputProgram D lowerCodeProgram) (liftNumericalProgram nodeFieldProgram))
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
    They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
    and compute the derivative-program index $\delta(e)$. Decode
    $w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
    $$\begin{aligned}
     B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
     C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
     L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
       (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
     V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
     M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
    \end{aligned}$$
    Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
    arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.
-/
def derivativeRunProgram (D I : AlphaTerm) :=
  dataInputProgram (derivativeEvalProgram D) (lowerReaderProgram I)

theorem derivativeEvalProgram_closed {D : AlphaTerm} (hD : D.Closed) :
    (derivativeEvalProgram D).Closed := relativeComposeProgram_closed uniformInterpreterProgram_closed
      (pairOutputProgram_closed (mapOutputProgram_closed hD lowerCodeProgram_closed)
        rankNodeField_computes.uniform.1)

theorem derivativeRunProgram_closed {D I : AlphaTerm} {i : ℕ → ℕ}
    (hD : D.Closed) (hI : NumericalComputes I i) : (derivativeRunProgram D I).Closed :=
  dataInputProgram_closed (derivativeEvalProgram_closed hD) (lowerReaderProgram_closed hI)

theorem derivativeRunProgram_runs {D I : AlphaTerm} {d i : ℕ → ℕ}
    (hD : NumericalComputes D d) (hI : NumericalComputes I i)
    {q : ℕ} {r : ℕ → ℕ} (hq : NumericalComputes (Term.closedProgram q) r)
    {ε η : ℕ → ℕ} (a s b m : ℕ)
    (hreader : ∀ k, OracleRuns ε (Term.closedProgram (i a)) (Nat.pair b k) (η k))
    (hvalue : OracleRuns η (Term.closedProgram (d (r b))) s m) :
    OracleRuns ε (derivativeRunProgram D I) (rankInput q a 0 s b) m := by
  let z := rankInput q a 0 s b
  have hc : OracleRuns η lowerCodeProgram z (r b) := by
    have hp := ((projection_computes true).pair lowerField_computes).uniform.2 η z
    have hs := (uncurryNumerical_start outputSearchTerm_closed (Nat.pair q b))
    simp only [Nat.unpair_pair] at hs
    have he := hs.trans ((outputSearchTerm_runs_iff q b (r b)).mpr (hq.2 b))
    apply mapOutputProgram_runs (uncurryNumerical_closed outputSearchTerm_closed)
      (((projection_computes true).pair lowerField_computes).uniform.1) _ he
    simpa only [z,rankInput,lowerField,Nat.unpair_pair,ite_true] using hp
  have hd := mapOutputProgram_runs hD.1 lowerCodeProgram_closed hc (hD.2 (r b))
  have hn : OracleRuns η (liftNumericalProgram nodeFieldProgram) z s := by
    simpa only [z,rankInput,nodeField,Nat.unpair_pair] using rankNodeField_computes.uniform.2 η z
  have he := relativeComposeProgram_runs uniformInterpreterProgram_closed
    (pairOutputProgram_closed (mapOutputProgram_closed hD.1 lowerCodeProgram_closed)
      rankNodeField_computes.uniform.1)
    (pairOutputProgram_runs (mapOutputProgram_closed hD.1 lowerCodeProgram_closed)
      rankNodeField_computes.uniform.1 hd hn)
    ((uniformInterpreterProgram_runs_iff η (d (r b)) s m).mpr hvalue)
  apply dataInputProgram_runs_of (derivativeEvalProgram_closed hD.1) (lowerReaderProgram_closed hI) he
  intro k
  have hinput := (readerInputProgram_computes hI).2 (Nat.pair z k)
  simp only [z,rankInput,stageField,lowerField,Nat.unpair_pair] at hinput
  exact reindexProgram_runs uniformInterpreterProgram_closed (readerInputProgram_computes hI).1
    ε (Nat.pair z k) _ _ hinput
    ((uniformInterpreterProgram_runs_iff ε (i a) (Nat.pair b k) (η k)).mpr (hreader k))

def baseReaderInputProgram (I : AlphaTerm) := pairNumerical
  (numericalCompose I (numericalCompose stageFieldProgram (numericalProjectionTerm true)))
  (pairNumerical (numericalCompose stageFieldProgram (numericalProjectionTerm true)) (numericalProjectionTerm false))
def baseReaderProgram (I : AlphaTerm) := reindexProgram uniformInterpreterProgram (baseReaderInputProgram I)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
    They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
    and compute the derivative-program index $\delta(e)$. Decode
    $w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
    $$\begin{aligned}
     B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
     C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
     L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
       (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
     V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
     M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
    \end{aligned}$$
    Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
    arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.
-/
def initialRunProgram (P I : AlphaTerm) :=
  dataInputProgram (reindexProgram P nodeFieldProgram) (baseReaderProgram I)

theorem baseReaderInputProgram_computes {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i) :
    NumericalComputes (baseReaderInputProgram I)
      (fun z => Nat.pair (i (stageField z.unpair.1)) (Nat.pair (stageField z.unpair.1) z.unpair.2)) :=
  (hi.comp (stageField_computes.comp (projection_computes true))).pair
    ((stageField_computes.comp (projection_computes true)).pair (projection_computes false))
theorem baseReaderProgram_closed {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i) :
    (baseReaderProgram I).Closed := reindexProgram_closed uniformInterpreterProgram_closed
      (baseReaderInputProgram_computes hi).1
theorem initialRunProgram_closed {P I : AlphaTerm} {i : ℕ → ℕ}
    (hP : P.Closed) (hI : NumericalComputes I i) : (initialRunProgram P I).Closed :=
  dataInputProgram_closed (reindexProgram_closed hP rankNodeField_computes.1) (baseReaderProgram_closed hI)

theorem initialRunProgram_runs {P I : AlphaTerm} {i : ℕ → ℕ}
    (hP : P.Closed) (hI : NumericalComputes I i) {ε η : ℕ → ℕ} (q a s b m : ℕ)
    (hreader : ∀ k, OracleRuns ε (Term.closedProgram (i a)) (Nat.pair a k) (η k))
    (hvalue : OracleRuns η P s m) :
    OracleRuns ε (initialRunProgram P I) (rankInput q a 0 s b) m := by
  let z := rankInput q a 0 s b
  have hn : Relation.ReflTransGen Beta (app nodeFieldProgram (numeral z)) (numeral s) := by
    simpa only [z,rankInput,nodeField,Nat.unpair_pair] using rankNodeField_computes.2 z
  have he := reindexProgram_runs hP rankNodeField_computes.1 η z s m hn hvalue
  apply dataInputProgram_runs_of (reindexProgram_closed hP rankNodeField_computes.1)
    (baseReaderProgram_closed hI) he
  intro k
  have hinput := (baseReaderInputProgram_computes hI).2 (Nat.pair z k)
  simp only [z,rankInput,stageField,Nat.unpair_pair] at hinput
  exact reindexProgram_runs uniformInterpreterProgram_closed (baseReaderInputProgram_computes hI).1
    ε (Nat.pair z k) _ _ hinput
    ((uniformInterpreterProgram_runs_iff ε (i a) (Nat.pair a k) (η k)).mpr (hreader k))

def expandStageInput (z : ℕ) := rankInput z.unpair.1 (stageField z) 0 z.unpair.2.unpair.2.unpair.1 (lowerField z)
def expandStageInputProgram := pairNumerical (numericalProjectionTerm true)
  (pairNumerical stageFieldProgram (pairNumerical
    (pairNumerical (numericalConstant 0) (numericalCompose (numericalProjectionTerm true) payloadProgram))
    lowerFieldProgram))
theorem expandStageInput_computes : NumericalComputes expandStageInputProgram expandStageInput :=
  (projection_computes true).pair (stageField_computes.pair
    (((numericalConstant_computes 0).pair ((projection_computes true).comp
      ((projection_computes false).comp (projection_computes false)))).pair lowerField_computes))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
    They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
    and compute the derivative-program index $\delta(e)$. Decode
    $w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
    $$\begin{aligned}
     B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
     C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
     L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
       (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
     V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
     M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
    \end{aligned}$$
    Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
    arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.
-/
def stageGuardProgram (C D I : AlphaTerm) :=
  ifZeroProgram (lowerTestProgram C) (constantProgram 1) (derivativeRunProgram D I)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
    They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
    and compute the derivative-program index $\delta(e)$. Decode
    $w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
    $$\begin{aligned}
     B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
     C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
     L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
       (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
     V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
     M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
    \end{aligned}$$
    Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
    arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.
-/
def stageMatrixProgram (P C D I : AlphaTerm) := reindexProgram
  (conjunctionProgram (initialRunProgram P I) (stageGuardProgram C D I)) expandStageInputProgram

theorem stageGuardProgram_closed {C D I : AlphaTerm} {c i : ℕ → ℕ}
    (hC : NumericalComputes C c) (hD : D.Closed) (hI : NumericalComputes I i) :
    (stageGuardProgram C D I).Closed := ifZeroProgram_closed (lowerTest_computes hC).1
      (constantProgram_closed 1) (derivativeRunProgram_closed hD hI)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
    They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
    and compute the derivative-program index $\delta(e)$. Decode
    $w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
    $$\begin{aligned}
     B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
     C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
     L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
       (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
     V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
     M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
    \end{aligned}$$
    Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
    arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.
-/
theorem stageMatrixProgram_closed {P C D I : AlphaTerm} {c i : ℕ → ℕ}
    (hP : P.Closed) (hC : NumericalComputes C c) (hD : D.Closed) (hI : NumericalComputes I i) :
    (stageMatrixProgram P C D I).Closed := reindexProgram_closed
      (conjunctionProgram_closed (initialRunProgram_closed hP hI) (stageGuardProgram_closed hC hD hI))
      expandStageInput_computes.1

/-- The fixed derivative compiler is not an input-dependent representative choice. -/
theorem stageMatrixProgram_subst (P C D I V : AlphaTerm) (hD : D.Closed) (hV : V.Closed)
    (x : ℕ) (hx : 43 < x) :
    (stageMatrixProgram P C D I).subst x V =
      stageMatrixProgram (P.subst x V) (C.subst x V) D (I.subst x V) := by
  have hv (i : ℕ) : i ∉ V.fv := by rw [hV]; simp
  have h1 : 1 ≠ x := by omega
  have h2 : 2 ≠ x := by omega
  have h40 : 40 ≠ x := by omega
  have h41 : 41 ≠ x := by omega
  have h42 : 42 ≠ x := by omega
  have h43 : 43 ≠ x := by omega
  have hmul := ((projection_computes true).mul (projection_computes false)).1
  simp only [stageMatrixProgram,stageGuardProgram,conjunctionProgram,initialRunProgram,
    baseReaderProgram,baseReaderInputProgram,derivativeRunProgram,derivativeEvalProgram,
    lowerReaderProgram,readerInputProgram,lowerTestProgram,
    dataInputProgram,dataInputAccessor,reindexProgram,relativeComposeProgram,
    mapOutputProgram,pairOutputProgram,liftNumericalProgram,ifZeroProgram,
    pairNumerical,numericalCombine,numericalCompose,
    subst_lam_fresh _ _ 1 x h1 (hv 1),subst_lam_fresh _ _ 2 x h2 (hv 2),
    subst_lam_fresh _ _ 40 x h40 (hv 40),subst_lam_fresh _ _ 41 x h41 (hv 41),
    subst_lam_fresh _ _ 42 x h42 (hv 42),subst_lam_fresh _ _ 43 x h43 (hv 43),
    subst_app,subst_closed _ _ _ hD,subst_closed _ _ _ hmul,
    subst_closed _ _ _ expandStageInput_computes.1,subst_closed _ _ _ lowerCodeProgram_closed,
    subst_closed _ _ _ uniformInterpreterProgram_closed,subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ zeroTestTerm_closed,subst_closed _ _ _ (constantProgram_closed 1),
    subst_closed _ _ _ rankNodeField_computes.1,subst_closed _ _ _ stageField_computes.1,
    subst_closed _ _ _ lowerField_computes.1,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_var,h1,h2,h40,h41,h42,h43,ite_false]

/-- The tree, predecessor-test, and reader-index programs are supplied by syntax codes. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform Cantor stage-template indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Replace the initial-tree program, predecessor test, and reader-index program in the composite template by three
    fresh free variables. Keep the derivative compiler fixed and choose one named representative of this open template.
    Successive capture-avoiding substitutions of the three decoded inputs compute $m(p,c,i)$. For closed inserted
    terms, substitution commutes with the displayed composition, input-substitution, and conditional constructors;
    their fresh binders cannot capture the inserted terms. Thus the result is precisely the composite stage program.
    The closure lemmas for these constructors show that it is closed under the stated hypotheses.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $q,r$ be the uniform self-indexed universal-family maps from §{sec:lambda-rank-decision-programs}. Put
    $$\begin{aligned}
    q_0(p,c,i)&:=q(m(p,c,i)),\\
    r_0(p,c,i,a)&:=r(m(p,c,i),a).
    \end{aligned}$$
    Numerical composition proves totality of both maps on all inputs. The self-indexed family theorem supplies the
    stated numerical computation for every triple and the conditional decision assertion for the closed matrix.
    These computations construct syntax; they run neither a tree test nor a lower-stage program.
-/
theorem uniform_stage_matrix_indices (D : AlphaTerm) (hD : D.Closed) :
    ∃ F f, NumericalComputes F f ∧ ∀ p c i,
      (Term.decode p).fv = ∅ → (Term.decode c).fv = ∅ → (Term.decode i).fv = ∅ →
      ∀ k l, NumericalComputes (Term.closedProgram c) k → NumericalComputes (Term.closedProgram i) l →
        (Term.decode (f (Nat.pair (Nat.pair p c) i))).fv = ∅ ∧
        Term.closedProgram (f (Nat.pair (Nat.pair p c) i)) =
          stageMatrixProgram (Term.closedProgram p) (Term.closedProgram c) D (Term.closedProgram i) := by
  obtain ⟨F,f,hF,hf⟩ := uniform_ternary_template_indices
    (stageMatrixProgram (var 86) (var 87) D (var 88)) 86 87 88
  refine ⟨F,f,hF,fun p c i hp hc hi k l hC hI => ?_⟩
  have hpp : mk (Term.decode p) = Term.closedProgram p := (ite_eq_left hp).symm
  have hcp : mk (Term.decode c) = Term.closedProgram c := (ite_eq_left hc).symm
  have hip : mk (Term.decode i) = Term.closedProgram i := (ite_eq_left hi).symm
  have ht := hf p c i
  rw [hpp,hcp,hip,stageMatrixProgram_subst _ _ _ _ _ hD (Term.closedProgram_closed p) 86 (by decide),
    stageMatrixProgram_subst _ _ _ _ _ hD hC.1 87 (by decide),
    stageMatrixProgram_subst _ _ _ _ _ hD hI.1 88 (by decide)] at ht
  norm_num only [subst_var,ite_true,ite_false,subst_closed _ _ _ (Term.closedProgram_closed p),
    subst_closed _ _ _ hC.1] at ht
  have hclosed : (Term.decode (f (Nat.pair (Nat.pair p c) i))).fv = ∅ := by
    change (mk (Term.decode (f (Nat.pair (Nat.pair p c) i)))).Closed
    rw [ht]
    exact stageMatrixProgram_closed (Term.closedProgram_closed p) hC hD hI
  exact ⟨hclosed,(ite_eq_left hclosed).trans ht⟩

/-- Composition with self-reference does not execute the matrix or any lower-stage program. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform Cantor stage-template indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The self-indexed universal-family construction applied to this $M$ produces the total index
    function $r$. In §{sec:edst-effective-cb}, the five-jump readers and well-founded induction verify
    the hypotheses of the lemma at every stage. The final universal quantifier costs one jump of
    the common upper input.
-/
theorem uniform_stage_index_families (D : AlphaTerm) (hD : D.Closed) :
    ∃ (Q R : AlphaTerm) (q r : ℕ → ℕ), NumericalComputes Q q ∧ NumericalComputes R r ∧
      (∀ w, NumericalComputes (Term.closedProgram (q w)) (fun a => r (Nat.pair w a))) ∧
      ∀ p c i, (Term.decode p).fv = ∅ → (Term.decode c).fv = ∅ → (Term.decode i).fv = ∅ →
        ∀ k l, NumericalComputes (Term.closedProgram c) k → NumericalComputes (Term.closedProgram i) l →
          ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → Prop),
            Decides ε (specializePairProgram (specializePairProgram
              (stageMatrixProgram (Term.closedProgram p) (Term.closedProgram c) D (Term.closedProgram i))
              (q (Nat.pair (Nat.pair p c) i))) a) (fun z : ℕ => M z.unpair.1 z.unpair.2) →
            Decides (jumpName ε) (Term.closedProgram (r (Nat.pair (Nat.pair (Nat.pair p c) i) a)))
              (fun n => ∀ b, M n b) := by
  obtain ⟨F,f,hF,hf⟩ := uniform_stage_matrix_indices D hD
  obtain ⟨Q₀,R₀,q₀,r₀,hQ₀,hR₀,hself,h⟩ := uniform_universally_quantified_self_families
  have hQ := hQ₀.comp hF
  have hR := hR₀.comp ((hF.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨_,_,fun w => q₀ (f w),fun z => r₀ (Nat.pair (f z.unpair.1) z.unpair.2),
    hQ,hR,?_,fun p c i hp hc hi k l hC hI a ε M hd => ?_⟩
  · intro w
    simpa only [Nat.unpair_pair] using hself (f w)
  · obtain ⟨hclosed,hprog⟩ := hf p c i hp hc hi k l hC hI
    simpa only [Nat.unpair_pair] using h (f (Nat.pair (Nat.pair p c) i)) hclosed a ε M (by rwa [hprog])

private theorem conjunction_runs {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    {ε : ℕ → ℕ} {z a b : ℕ} (hp : OracleRuns ε P z a) (hq : OracleRuns ε Q z b) :
    OracleRuns ε (conjunctionProgram P Q) z (a*b) := by
  have hM := (projection_computes true).mul (projection_computes false)
  have h := mapOutputProgram_runs hM.1 (pairOutputProgram_closed hP hQ)
    (pairOutputProgram_runs hP hQ hp hq) (hM.2 (Nat.pair a b))
  simpa only [conjunctionProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Guarded derivative-stage evaluation
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For each query numeral, the first reader supplies the value of $\eta$. Input substitution therefore
    reduces the first factor to the decision bit for $U(s)$. If the predecessor test returns zero,
    the zero test returns one without executing $L$. Otherwise, pure universal evaluation supplies
    $r(b)$, and the numerical derivative compiler supplies $\delta(r(b))$. Substituting the second
    reader for each input query in that program gives its decision bit for $V_b(s)$. Multiplication
    of the two bits gives the displayed conjunction. All invoked computations terminate by the
    hypotheses; no lower program is executed outside the predecessor set. Pair-specialization
    preserves these beta/query reductions.
    \end{proof}
-/
theorem stageMatrixProgram_decides {P C D I : AlphaTerm} {c : ℕ → ℕ → Prop} {i : ℕ → ℕ}
    (hP : P.Closed) (hC : NumericalComputes C (fun z => if c z.unpair.1 z.unpair.2 then 1 else 0))
    (hD : D.Closed) (hI : NumericalComputes I i)
    (q a : ℕ) (ε : ℕ → ℕ) (T : ℕ → Prop) (L : ℕ → ℕ → Prop)
    (hp : ∀ s b, OracleRuns ε (initialRunProgram P I) (rankInput q a 0 s b) (if T s then 1 else 0))
    (hl : ∀ s b, c b a → OracleRuns ε (derivativeRunProgram D I)
      (rankInput q a 0 s b) (if L b s then 1 else 0)) :
    Decides ε (specializePairProgram (specializePairProgram (stageMatrixProgram P C D I) q) a)
      (fun z : ℕ => T z.unpair.1 ∧ (c z.unpair.2 a → L z.unpair.2 z.unpair.1)) := by
  have hG := stageGuardProgram_closed hC hD hI
  have hN := initialRunProgram_closed hP hI
  have hM := stageMatrixProgram_closed hP hC hD hI
  have hm (s b : ℕ) : OracleRuns ε (stageMatrixProgram P C D I)
      (Nat.pair q (Nat.pair a (Nat.pair s b))) (if T s ∧ (c b a → L b s) then 1 else 0) := by
    have hg : OracleRuns ε (stageGuardProgram C D I) (rankInput q a 0 s b)
        (if c b a → L b s then 1 else 0) := by
      have hc := (lowerTest_computes hC).2 (rankInput q a 0 s b)
      simp only [rankInput,lowerField,stageField,Nat.unpair_pair] at hc
      by_cases hb : c b a
      · apply ifZeroProgram_runs_one (lowerTest_computes hC).1 (constantProgram_closed 1)
          (derivativeRunProgram_closed hD hI) (by simpa only [rankInput,ite_eq_left hb] using hc)
        simpa only [hb,true_implies] using hl s b hb
      · apply ifZeroProgram_runs_zero (lowerTest_computes hC).1 (constantProgram_closed 1)
          (derivativeRunProgram_closed hD hI) (by simpa only [rankInput,ite_eq_right hb] using hc)
        simpa only [hb,false_implies,ite_true] using constantProgram_runs 1 ε (rankInput q a 0 s b)
    have hh := conjunction_runs hN hG (hp s b) hg
    have hv : (if T s then 1 else 0) * (if c b a → L b s then 1 else 0) =
        (if T s ∧ (c b a → L b s) then 1 else 0) := by split_ifs <;> simp_all
    rw [hv] at hh
    apply reindexProgram_runs (conjunctionProgram_closed hN hG) expandStageInput_computes.1 _ _ _ _ _ hh
    simpa only [expandStageInput,rankInput,stageField,lowerField,Nat.unpair_pair]
      using expandStageInput_computes.2 (Nat.pair q (Nat.pair a (Nat.pair s b)))
  refine ⟨specializePairProgram_closed (specializePairProgram_closed hM q) a,fun z => ?_⟩
  have h := specializePairProgram_runs (specializePairProgram_closed hM q)
    (specializePairProgram_runs hM (hm z.unpair.1 z.unpair.2))
  simp only [Nat.pair_unpair] at h
  constructor <;> intro hz
  · simpa only [ite_eq_left hz,Encodable.encode_nat] using h
  · simpa only [ite_eq_right hz,Encodable.encode_nat] using h

end CantorDerivative
end PolishSpaceBook
