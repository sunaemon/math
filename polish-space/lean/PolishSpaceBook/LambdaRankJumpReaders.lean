module

public import PolishSpaceBook.LambdaJumpReaderIndices
public import PolishSpaceBook.LambdaNotationCoverage
public import PolishSpaceBook.LambdaJumpQuantifiers

@[expose] public section

/-! # A computed family of oracle readers for rank recursion

At stage a the upper notation dominates every fixed finite successor iterate
of every predecessor notation. Nonpredecessors use the base row, making each numerical family
total on the actual well-order domain. The code generator is total everywhere.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace KleeneNotation
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

noncomputable def predecessorNotation (W : WellOrderPresentation (fun _ => 0))
    (g : ℕ → ℕ) (z : ℕ) (depth : ℕ := 2) : ℕ :=
  if W.domain z.unpair.2 ∧ W.relation z.unpair.2 z.unpair.1
  then iterateSuccessor (g z.unpair.2) depth else 1

theorem predecessorNotation_computable (W : WellOrderPresentation (fun _ => 0))
    {G : AlphaTerm} {g : ℕ → ℕ} (hG : NumericalComputes G g) (depth : ℕ := 2) :
    ∃ L, NumericalComputes L (fun z => predecessorNotation W g z depth) := by
  have hd := W.domain_decidable.precompNumerical (projection_computes false)
    (g := fun z : ℕ => z.unpair.2) (by simp)
  have hr := W.relation_decidable.precompNumerical
    ((projection_computes false).pair (projection_computes true))
    (g := fun z : ℕ => (z.unpair.2,z.unpair.1)) (by simp)
  obtain ⟨C,hC⟩ := hd.and hr
  have ht := hC.toPure (numericalConstant_computes 0)
  have hc : NumericalComputes (app C (numericalConstant 0))
      (fun z : ℕ => if W.domain z.unpair.2 ∧ W.relation z.unpair.2 z.unpair.1 then 1 else 0) := by
    refine ⟨ht.1,fun z => ?_⟩
    dsimp only
    split_ifs with hz
    · exact (ht.2 z).1 hz
    · exact (ht.2 z).2 hz
  have hs := iterateSuccessorProgram_computes.comp
    ((hG.comp (projection_computes false)).pair (numericalConstant_computes depth))
  have h := hc.ifLe (numericalConstant_computes 0) (numericalConstant_computes 1) hs
  refine ⟨_,h.1,fun z => ?_⟩
  by_cases hz : W.domain z.unpair.2 ∧ W.relation z.unpair.2 z.unpair.1 <;>
    simpa [predecessorNotation,hz] using h.2 z

def predecessorTestTemplate (D R : AlphaTerm) : AlphaTerm :=
  mulNumerical (numericalCompose D (numericalProjectionTerm true)) R

theorem predecessorTestTemplate_subst (D R P : AlphaTerm) (hP : P.Closed)
    (x : ℕ) (hx : 40 < x) :
    (predecessorTestTemplate D R).subst x P =
      predecessorTestTemplate (D.subst x P) (R.subst x P) := by
  have h40 : 40 ≠ x := by omega
  have hp : 40 ∉ P.fv := by rw [hP]; simp
  simp only [predecessorTestTemplate,mulNumerical,numericalCombine,numericalCompose,
    subst_lam_fresh _ _ 40 x h40 hp,subst_app,subst_var,h40,ite_false,
    subst_closed _ _ _ multiplicationTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true)]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The predecessor-test index can itself be obtained from decision-program indices $d,t$. Compose the domain
    program with the first numerical projection and multiply its output by the relation program's output.
    For correct bit deciders this is one exactly when the first number belongs to the domain and precedes the second.
    Fix this two-variable template once. Two successive syntax substitutions give a total index map $\kappa(d,t)$
    for the predecessor test. No well-foundedness test is part of this construction.
-/
theorem uniform_predecessor_test_indices :
    ∃ C c, NumericalComputes C c ∧ ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r,
      (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
      NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
      NumericalComputes (Term.closedProgram r)
        (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
      (Term.decode (c (Nat.pair d r))).fv = ∅ ∧
      NumericalComputes (Term.closedProgram (c (Nat.pair d r)))
        (fun z => if W.domain z.unpair.1 ∧ W.relation z.unpair.1 z.unpair.2 then 1 else 0) := by
  obtain ⟨C,c,hC,hc⟩ := uniform_binary_template_indices
    (predecessorTestTemplate (var 86) (var 87)) 86 87
  refine ⟨C,c,hC,fun W d r hd hr hD hR => ?_⟩
  have hdp : mk (Term.decode d) = Term.closedProgram d := (ite_eq_left hd).symm
  have hrp : mk (Term.decode r) = Term.closedProgram r := (ite_eq_left hr).symm
  have ht := hc d r
  rw [hdp,hrp,predecessorTestTemplate_subst _ _ _ hD.1 86 (by decide),
    predecessorTestTemplate_subst _ _ _ hR.1 87 (by decide)] at ht
  norm_num only [subst_var,ite_true,ite_false,subst_closed _ _ _ hD.1] at ht
  have hcomp := (hD.comp (projection_computes true)).mul hR
  have hclosed : (Term.decode (c (Nat.pair d r))).fv = ∅ := by
    change (mk (Term.decode (c (Nat.pair d r)))).Closed
    rw [ht]
    exact hcomp.1
  have hp : Term.closedProgram (c (Nat.pair d r)) =
      predecessorTestTemplate (Term.closedProgram d) (Term.closedProgram r) := (ite_eq_left hclosed).trans ht
  refine ⟨hclosed,?_⟩
  rw [hp]
  refine ⟨hcomp.1,fun z => ?_⟩
  by_cases hd : W.domain z.unpair.1 <;> by_cases hr : W.relation z.unpair.1 z.unpair.2 <;>
    simpa [predecessorTestTemplate,hd,hr] using hcomp.2 z

/-- Input is the pair of the jump depth and the pair of stage and candidate predecessor. -/
def predecessorNotationTemplate (D R G : AlphaTerm) : AlphaTerm :=
  let K := numericalProjectionTerm true
  let A := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let B := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalIfLe (numericalCompose D B) (numericalConstant 0) (numericalConstant 1)
    (numericalIfLe (numericalCompose R (pairNumerical B A))
      (numericalConstant 0) (numericalConstant 1)
      (numericalCompose iterateSuccessorProgram (pairNumerical (numericalCompose G B) K)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use numerical projections to read $k,a,b$ from $\NatPair{k}{\NatPair{a}{b}}$.
    The finite successor-iteration term from §{sec:lambda-recursive-order-programs} computes
    $\KleeneSuccIter{g(b)}{k}$ from the output of the third program and the first projection.
    Apply the numerical conditional twice: if the domain bit is at most zero, return one; otherwise, if the
    relation bit is at most zero, return one; otherwise return that successor iterate. All component computations
    terminate under the hypotheses, and the two bit tests give exactly the displayed cases.
-/
theorem predecessorNotationTemplate_computes (W : WellOrderPresentation (fun _ => 0))
    {D R G : AlphaTerm} {g : ℕ → ℕ}
    (hD : NumericalComputes D (fun n => if W.domain n then 1 else 0))
    (hR : NumericalComputes R (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0))
    (hG : NumericalComputes G g) :
    NumericalComputes (predecessorNotationTemplate D R G)
      (fun z => predecessorNotation W g z.unpair.2 z.unpair.1) := by
  have hk := projection_computes true
  have ha := (projection_computes true).comp (projection_computes false)
  have hb := (projection_computes false).comp (projection_computes false)
  have hs := iterateSuccessorProgram_computes.comp ((hG.comp hb).pair hk)
  have h := (hD.comp hb).ifLe (numericalConstant_computes 0) (numericalConstant_computes 1)
    ((hR.comp (hb.pair ha)).ifLe (numericalConstant_computes 0) (numericalConstant_computes 1) hs)
  refine ⟨h.1,fun z => ?_⟩
  by_cases hd : W.domain z.unpair.2.unpair.2 <;>
    by_cases hr : W.relation z.unpair.2.unpair.2 z.unpair.2.unpair.1 <;>
    simpa [predecessorNotationTemplate,predecessorNotation,hd,hr] using h.2 z

theorem predecessorNotationTemplate_subst (D R G P : AlphaTerm) (hP : P.Closed)
    (x : ℕ) (hx : 40 < x) :
    (predecessorNotationTemplate D R G).subst x P =
      predecessorNotationTemplate (D.subst x P) (R.subst x P) (G.subst x P) := by
  have hp (i : ℕ) : i ∉ P.fv := by rw [hP]; simp
  have h40 : 40 ≠ x := by omega
  simp only [predecessorNotationTemplate,numericalIfLe,numericalCompose,numericalConstant,
    pairNumerical,numericalCombine,subst_lam_fresh _ _ 40 x h40 (hp 40),subst_app,
    chooseLeBody_subst,subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ iterateSuccessorProgram_computes.1,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_closed _ _ _ (numeral_closed 0),subst_closed _ _ _ (numeral_closed 1),
    subst_var,h40,ite_false]

/-- All three program indices and the finite jump depth are supplied numerically. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform predecessor-notation indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Build this composite term using three fresh free variables in place of the domain, relation, and upper-notation
    programs, and fix a named representative once. Three successive capture-avoiding substitutions from
    §{sec:lambda-code-substitution} compute its code $\eta(d,r,e)$. Each substitution receives the code produced by
    the preceding substitution. The numerical parameter construction in §{sec:lambda-index-recursion} now gives
    $$\mu(d,r,e,k):=\sigma(\eta(d,r,e),k).$$
    This fixes the first component of the input and leaves the pair of stage and predecessor as the argument.
    Closed input programs give a closed output program. Substitution and parameter insertion do not execute the
    supplied programs, so code generation terminates even when a decision or totality hypothesis fails.
-/
theorem uniform_predecessor_notation_indices :
    ∃ L l, NumericalComputes L l ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r e,
        (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ → (Term.decode e).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram r)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∀ g, NumericalComputes (Term.closedProgram e) g → ∀ k,
          (Term.decode (l (Nat.pair (Nat.pair (Nat.pair d r) e) k))).fv = ∅ ∧
          NumericalComputes (Term.closedProgram (l (Nat.pair (Nat.pair (Nat.pair d r) e) k)))
            (fun z => predecessorNotation W g z k) := by
  obtain ⟨F,f,hF,hf⟩ := uniform_ternary_template_indices
    (predecessorNotationTemplate (var 86) (var 87) (var 88)) 86 87 88
  obtain ⟨S,s,hS,hs⟩ := uniform_numerical_parameter_indices
  have hL := hS.comp ((hF.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨_,fun z => s (Nat.pair (f z.unpair.1) z.unpair.2),hL,
    fun W d r e hd hr he hD hR g hG k => ?_⟩
  have hdp : mk (Term.decode d) = Term.closedProgram d := (ite_eq_left hd).symm
  have hrp : mk (Term.decode r) = Term.closedProgram r := (ite_eq_left hr).symm
  have hep : mk (Term.decode e) = Term.closedProgram e := (ite_eq_left he).symm
  have ht := hf d r e
  rw [hdp,hrp,hep,predecessorNotationTemplate_subst _ _ _ _ hD.1 86 (by decide),
    predecessorNotationTemplate_subst _ _ _ _ hR.1 87 (by decide),
    predecessorNotationTemplate_subst _ _ _ _ hG.1 88 (by decide)] at ht
  norm_num only [subst_var,ite_true,ite_false,subst_closed _ _ _ hD.1,
    subst_closed _ _ _ hR.1] at ht
  have hT := predecessorNotationTemplate_computes W hD hR hG
  have hc : (Term.decode (f (Nat.pair (Nat.pair d r) e))).fv = ∅ := by
    change (mk (Term.decode (f (Nat.pair (Nat.pair d r) e)))).Closed
    rw [ht]
    exact hT.1
  have hprog : Term.closedProgram (f (Nat.pair (Nat.pair d r) e)) =
      predecessorNotationTemplate (Term.closedProgram d) (Term.closedProgram r) (Term.closedProgram e) :=
    (ite_eq_left hc).trans ht
  obtain ⟨hc',_,h⟩ := hs (f (Nat.pair (Nat.pair d r) e)) k hc
  have hp := h _ (by rw [hprog]; exact hT)
  simpa only [Nat.unpair_pair] using And.intro hc' hp

/-- Decision indices, jump depth, and stage all enter one total reader-index map. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Uniform rank readers from decision indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Use the index map $e(d,r)$ from §{sec:edst-ordinal-notations}. The lower-notation compiler and reader compiler
    in §{sec:lambda-certified-descent} give total maps $\mu$ and $\psi$. Put
    $$i(d,r,k,a):=\psi\bigl(e(d,r),\mu(d,r,e(d,r),k),a\bigr).$$
    Numerical composition computes this index from the four inputs. Under the decision hypotheses, the lower-notation
    program selects the specified finite successor iterate at each predecessor and the base notation otherwise.
    The upper-notation construction provides a finite certified path from each selected notation to the upper one.
    Apply the reader theorem to the canonical jump table. Repeated successor equations identify the selected row
    with the required finite jump; the base equation handles nonpredecessors. These arguments work for every
    starting set. The reader searches for a path only when executed: producing its index uses composition and
    syntax operations alone.
-/
theorem uniform_order_reader_indices :
    ∃ (E I : AlphaTerm) (e i g : ℕ → ℕ), NumericalComputes E e ∧ NumericalComputes I i ∧
      (∀ z, (Term.decode (e z)).fv = ∅ ∧
        NumericalComputes (Term.closedProgram (e z)) (fun a => g (Nat.pair z a))) ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r,
        (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram r)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∀ k (a : W.Carrier),
          (Term.decode (i (Nat.pair (Nat.pair d r) (Nat.pair k a.val)))).fv = ∅ ∧
          Valid (g (Nat.pair (Nat.pair d r) a.val)) ∧
          ∀ (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q →
            tableDomain q (g (Nat.pair (Nat.pair d r) a.val)) →
            Computes (tableRow q (g (Nat.pair (Nat.pair d r) a.val)))
              (Term.closedProgram (i (Nat.pair (Nat.pair d r) (Nat.pair k a.val))))
              (fun z : ℕ => tableRow q
                (predecessorNotation W (fun b => g (Nat.pair (Nat.pair d r) b))
                  (Nat.pair a.val z.unpair.1) k) z.unpair.2) := by
  obtain ⟨E,e,g,hE,he,hg⟩ := uniform_upper_notation_program_indices
  obtain ⟨L,l,hL,hl⟩ := uniform_predecessor_notation_indices
  obtain ⟨J,j,hJ,hj⟩ := uniform_computed_reader_indices
  have hz := projection_computes true
  have hk := (projection_computes true).comp (projection_computes false)
  have ha := (projection_computes false).comp (projection_computes false)
  have hu := hE.comp hz
  have hlow := hL.comp ((hz.pair hu).pair hk)
  have hi := hJ.comp ((hu.pair hlow).pair ha)
  let i (z : ℕ) := j (Nat.pair
    (Nat.pair (e z.unpair.1) (l (Nat.pair (Nat.pair z.unpair.1 (e z.unpair.1)) z.unpair.2.unpair.1)))
    z.unpair.2.unpair.2)
  refine ⟨E,_,e,i,g,hE,hi,he,fun W d r hd hr hD hR k a => ?_⟩
  let g' (b : ℕ) := g (Nat.pair (Nat.pair d r) b)
  obtain ⟨hec,hG⟩ := he (Nat.pair d r)
  obtain ⟨hlc,hT⟩ := hl W d r (e (Nat.pair d r)) hd hr hec hD hR g' hG k
  obtain ⟨hv,_,hbase,hpred⟩ := hg W d r hd hr hD hR a
  have hpath (n : ℕ) : RawPrecedes (predecessorNotation W g' (Nat.pair a.val n) k) (g' a.val) := by
    simp only [predecessorNotation,Nat.unpair_pair]
    split_ifs with hn
    · exact hpred ⟨n,hn.1⟩ hn.2 k
    · exact hbase 0
  have h := hj (e (Nat.pair d r)) (l (Nat.pair (Nat.pair (Nat.pair d r) (e (Nat.pair d r))) k))
    hec hlc g' (fun z => predecessorNotation W g' z k) hG hT a.val
  simp only [i,Nat.unpair_pair]
  refine ⟨h.1,hv,fun A q hq hqa => ?_⟩
  exact h.2 A q hq hqa (fun n => AccessPath.exists_of_raw (hpath n))

/-- The lower rows may include any fixed finite number of jumps. -/
theorem recursive_order_reader_indices (W : WellOrderPresentation (fun _ => 0)) (depth : ℕ := 2) :
    ∃ (G I : AlphaTerm) (g i : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes I i ∧
      (∀ a : W.Carrier, Valid (g a.val)) ∧
      (∀ a : W.Carrier, ∀ n, RawPrecedes (predecessorNotation W g (Nat.pair a.val n) depth) (g a.val)) ∧
      ∀ (a : W.Carrier) (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q → tableDomain q (g a.val) →
        Computes (tableRow q (g a.val)) (Term.closedProgram (i a.val))
          (fun z : ℕ => tableRow q (predecessorNotation W g (Nat.pair a.val z.unpair.1) depth) z.unpair.2) := by
  obtain ⟨C,hC⟩ := W.exists_pure_predecessorMaximum
  obtain ⟨u,q,hq,hseq⟩ := exists_computed_upper_sequences hC
  let g := delayedLimit u q
  have hv := upperFamily_valid W u q hseq
  obtain ⟨L,hL⟩ := predecessorNotation_computable W hq depth
  obtain ⟨I,i,hI,hi⟩ := computed_reader_indices hq hL
  have hp (a : W.Carrier) (n : ℕ) :
      RawPrecedes (predecessorNotation W g (Nat.pair a.val n) depth) (g a.val) := by
    simp only [predecessorNotation,Nat.unpair_pair]
    split_ifs with hn
    · exact (hv a).2.2 ⟨n,hn.1⟩ hn.2 depth
    · exact (hv a).2.1 0
  refine ⟨Term.closedProgram q,I,g,i,hq,hI,fun a => (hv a).1,hp,?_⟩
  intro a A t ht ha
  exact hi a.val A t ht ha (fun n => AccessPath.exists_of_raw (hp a n))


/-- A finite number of jumps of an input name, with the iteration count fixed externally. -/
noncomputable def finiteJumpName (ε : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => ε
  | n+1 => jumpName (finiteJumpName ε n)

theorem characteristic_iterateSuccessor (A : Set ℕ) {a : ℕ} (ha : Valid a) (n : ℕ) :
    characteristic (iteratedJump A (iterateSuccessor a n) (iterateSuccessor_valid ha n)) =
      finiteJumpName (characteristic (iteratedJump A a ha)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change characteristic (iteratedJump A (successorCode (iterateSuccessor a n))
      (.succ (iterateSuccessor_valid ha n))) = _
    rw [iteratedJump_successor A _ (iterateSuccessor_valid ha n)]
    change jumpName _ = jumpName _
    rw [ih]

noncomputable def predecessorFiniteJumpRows (W : WellOrderPresentation (fun _ => 0))
    (g : ℕ → ℕ) (hv : ∀ a : W.Carrier, Valid (g a.val))
    (A : Set ℕ) (a : W.Carrier) (depth z : ℕ) : ℕ :=
  if h : W.domain z.unpair.1 ∧ W.relation z.unpair.1 a.val then
    finiteJumpName (characteristic (iteratedJump A (g z.unpair.1) (hv ⟨z.unpair.1,h.1⟩))) depth z.unpair.2
  else characteristic A z.unpair.2

/-- Canonical jump tables turn the uniform table readers into finite-jump readers. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Uniform rank readers from decision indices
-/
theorem uniform_order_finiteJump_readers :
    ∃ (E I : AlphaTerm) (e i g : ℕ → ℕ), NumericalComputes E e ∧ NumericalComputes I i ∧
      (∀ z, (Term.decode (e z)).fv = ∅ ∧
        NumericalComputes (Term.closedProgram (e z)) (fun a => g (Nat.pair z a))) ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r,
        (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram r)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∃ hv : ∀ a : W.Carrier, Valid (g (Nat.pair (Nat.pair d r) a.val)),
          ∀ k (a : W.Carrier) (A : Set ℕ),
            Computes (characteristic (iteratedJump A (g (Nat.pair (Nat.pair d r) a.val)) (hv a)))
              (Term.closedProgram (i (Nat.pair (Nat.pair d r) (Nat.pair k a.val))))
              (predecessorFiniteJumpRows W (fun b => g (Nat.pair (Nat.pair d r) b)) hv A a k) := by
  obtain ⟨E,I,e,i,g,hE,hI,he,h⟩ := uniform_order_reader_indices
  refine ⟨E,I,e,i,g,hE,hI,he,fun W d r hd hr hD hR => ?_⟩
  have hv (a : W.Carrier) : Valid (g (Nat.pair (Nat.pair d r) a.val)) :=
    (h W d r hd hr hD hR 0 a).2.1
  refine ⟨hv,fun k a A => ?_⟩
  have ht := (h W d r hd hr hD hR k a).2.2 A (canonicalJumpTable A)
    (canonicalJumpTable_spec A) ((canonicalJumpTable_domain A _).mpr (hv a))
  have heq : tableRow (canonicalJumpTable A) (g (Nat.pair (Nat.pair d r) a.val)) =
      characteristic (iteratedJump A _ (hv a)) := funext (canonicalJumpTable_row A _ (hv a))
  rw [heq] at ht
  have hout : (fun z : ℕ => tableRow (canonicalJumpTable A)
      (predecessorNotation W (fun b => g (Nat.pair (Nat.pair d r) b))
        (Nat.pair a.val z.unpair.1) k) z.unpair.2) =
      predecessorFiniteJumpRows W (fun b => g (Nat.pair (Nat.pair d r) b)) hv A a k := by
    funext z
    simp only [predecessorNotation,Nat.unpair_pair,predecessorFiniteJumpRows]
    split_ifs with hb
    · rw [canonicalJumpTable_row A _ (iterateSuccessor_valid (hv ⟨z.unpair.1,hb.1⟩) k),
        characteristic_iterateSuccessor]
    · rw [canonicalJumpTable_row A 1 .zero,iteratedJump_zero]
  rw [hout] at ht
  exact ht

/-- One numerical compiler supplies readers for any fixed finite jump depth. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The same reader construction works with any fixed number $k$ of successive jumps in place of two.
    Replace $\KleeneSuccIter{g(b)}{2}$ by $\KleeneSuccIter{g(b)}{k}$ in the predecessor notation.
    The upper-notation construction dominates every finite successor iterate of each predecessor
    notation, and the canonical jump table identifies this row by $k$ successor equations.
    Both index functions remain total and independent of the starting set.
-/
theorem recursive_order_finiteJump_readers (W : WellOrderPresentation (fun _ => 0)) (depth : ℕ) :
    ∃ (G I : AlphaTerm) (g i : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes I i ∧
      ∃ hv : ∀ a : W.Carrier, Valid (g a.val), ∀ (a : W.Carrier) (A : Set ℕ),
        Computes (characteristic (iteratedJump A (g a.val) (hv a))) (Term.closedProgram (i a.val))
          (predecessorFiniteJumpRows W g hv A a depth) := by
  obtain ⟨G,I,g,i,hG,hI,hv,hp,hi⟩ := recursive_order_reader_indices W depth
  refine ⟨G,I,g,i,hG,hI,hv,fun a A => ?_⟩
  have ht := hi a A (canonicalJumpTable A) (canonicalJumpTable_spec A)
    ((canonicalJumpTable_domain A (g a.val)).mpr (hv a))
  have he : tableRow (canonicalJumpTable A) (g a.val) =
      characteristic (iteratedJump A (g a.val) (hv a)) := funext (canonicalJumpTable_row A _ (hv a))
  rw [he] at ht
  have hout : (fun z : ℕ => tableRow (canonicalJumpTable A)
      (predecessorNotation W g (Nat.pair a.val z.unpair.1) depth) z.unpair.2) =
      predecessorFiniteJumpRows W g hv A a depth := by
    funext z
    simp only [predecessorNotation,Nat.unpair_pair,predecessorFiniteJumpRows]
    split_ifs with h
    · rw [canonicalJumpTable_row A _ (iterateSuccessor_valid (hv ⟨z.unpair.1,h.1⟩) depth),
        characteristic_iterateSuccessor]
    · rw [canonicalJumpTable_row A 1 .zero,iteratedJump_zero]
  rw [hout] at ht
  exact ht


noncomputable def predecessorJumpRows (W : WellOrderPresentation (fun _ => 0))
    (g : ℕ → ℕ) (hv : ∀ a : W.Carrier, Valid (g a.val))
    (A : Set ℕ) (a : W.Carrier) (z : ℕ) : ℕ :=
  match z.unpair with
  | (b,m) => if h : W.domain b ∧ W.relation b a.val then
      jumpName (jumpName (characteristic (iteratedJump A (g b) (hv ⟨b,h.1⟩)))) m
    else characteristic A m

/-- A total compiler, not an arbitrary choice of one program at each stage. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computed readers for rank recursion
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the total notation assignment $g$ constructed in §{sec:edst-ordinal-notations}. For $a\in D$, its
    simultaneous induction gives
    $$\begin{gathered}
    \KleeneCandidatePrecedes{1}{g(a)},\\
     b\in D,\ bRa\ \Longrightarrow
     \KleeneCandidatePrecedes{\KleeneSuccIter{g(b)}{2}}{g(a)}.
    \end{gathered}$$
    The numerical function
    $$\ell(a,b):=\begin{cases}
    \KleeneSuccIter{g(b)}{2}&b\in D,\ bRa,\\
    1&b\notin D\lor\neg(bRa)
    \end{cases}$$
    is total and computable: decide domain membership and comparison, compute $g(b)$ when needed, and apply
    the successor constructor twice. For $a\in D$, every $\ell(a,b)$ therefore has a finite certified path
    to $g(a)$. Choose syntax codes $e,h$ for closed terms computing $g$ and $\ell$. The reader-index construction
    in §{sec:lambda-certified-descent} gives a single total numerical map $\psi(e,h,a)$; put
    $$i(a):=\psi(e,h,a).$$
    The canonical jump table identifies its output row with $B_{a,b}$, by two successor equations in the predecessor
    case and the base equation otherwise. Producing $i(a)$ uses only the two program indices and the stage number;
    it neither searches for paths nor tests notation validity.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a recursive well order, the following construction supplies the input functions
    for the lower stages, together with a computable map of reader indices.
-/
theorem recursive_order_twoJump_readers (W : WellOrderPresentation (fun _ => 0)) :
    ∃ (G I : AlphaTerm) (g i : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes I i ∧
      ∃ hv : ∀ a : W.Carrier, Valid (g a.val), ∀ (a : W.Carrier) (A : Set ℕ),
        Computes (characteristic (iteratedJump A (g a.val) (hv a))) (Term.closedProgram (i a.val))
          (predecessorJumpRows W g hv A a) := by
  obtain ⟨G,I,g,i,hG,hI,hv,hp,hi⟩ := recursive_order_reader_indices W
  refine ⟨G,I,g,i,hG,hI,hv,fun a A => ?_⟩
  have ht := hi a A (canonicalJumpTable A) (canonicalJumpTable_spec A)
    ((canonicalJumpTable_domain A (g a.val)).mpr (hv a))
  have he : tableRow (canonicalJumpTable A) (g a.val) =
      characteristic (iteratedJump A (g a.val) (hv a)) := funext (canonicalJumpTable_row A _ (hv a))
  rw [he] at ht
  have hout : (fun z : ℕ => tableRow (canonicalJumpTable A)
      (predecessorNotation W g (Nat.pair a.val z.unpair.1)) z.unpair.2) =
      predecessorJumpRows W g hv A a := by
    funext z
    simp only [predecessorNotation,Nat.unpair_pair,predecessorJumpRows]
    split_ifs with h
    · rw [canonicalJumpTable_row A _ (iterateSuccessor_valid (hv ⟨z.unpair.1,h.1⟩) 2)]
      simp only [iterateSuccessor,jumpName]
      rw [iteratedJump_successor A _ (.succ (hv ⟨z.unpair.1,h.1⟩)),
        iteratedJump_successor A _ (hv ⟨z.unpair.1,h.1⟩)]
    · rw [canonicalJumpTable_row A 1 .zero,iteratedJump_zero]
  rw [hout] at ht
  exact ht

end KleeneNotation
end PolishSpaceBook
