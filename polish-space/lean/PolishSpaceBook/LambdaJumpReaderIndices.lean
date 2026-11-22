module

public import PolishSpaceBook.LambdaJumpPathSearch
public import PolishSpaceBook.LambdaTemplateIndices

@[expose] public section

/-! # Computable indices for readers with varying upper notations

One partial numerical search takes both endpoints as input. Its code, and
codes obtained by specializing a stage, are produced without establishing
validity or running that search. Correctness is conditional on a finite path.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Input ((b,a),m): find a path b to a, then compose its address changes. -/
def pathQueryAddress (C F : AlphaTerm) : AlphaTerm := lam 40
  (app F (app (app numericalPairTerm
    (app (numericalSearch C) (app (numericalProjectionTerm true) (var 40))))
    (app (numericalProjectionTerm false) (var 40))))

theorem pathQueryAddress_closed {C F : AlphaTerm} (hC : C.Closed) (hF : F.Closed) :
    (pathQueryAddress C F).Closed := by
  unfold pathQueryAddress Closed
  simp only [fv_lam,fv_app,fv_var,(show F.fv = ∅ from hF),
    (show (numericalSearch C).fv = ∅ from numericalSearch_closed hC),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    (show (numericalProjectionTerm true).fv = ∅ from numericalProjectionTerm_closed true),
    (show (numericalProjectionTerm false).fv = ∅ from numericalProjectionTerm_closed false)]
  decide

theorem pathQueryAddress_apply {C F : AlphaTerm} (hC : C.Closed) (hF : F.Closed)
    (b a m c r : ℕ)
    (hS : Relation.ReflTransGen Beta (app (numericalSearch C) (numeral (Nat.pair b a))) (numeral c))
    (hR : Relation.ReflTransGen Beta (app F (numeral (Nat.pair c m))) (numeral r)) :
    Relation.ReflTransGen Beta (app (pathQueryAddress C F) (numeral (Nat.pair (Nat.pair b a) m)))
      (numeral r) := by
  let n := Nat.pair (Nat.pair b a) m
  have hb : Beta (app (pathQueryAddress C F) (numeral n))
      (app F (app (app numericalPairTerm
        (app (numericalSearch C) (app (numericalProjectionTerm true) (numeral n))))
        (app (numericalProjectionTerm false) (numeral n)))) := by
    simpa only [pathQueryAddress,subst_app,subst_var,ite_true,
      subst_closed _ _ _ hF,subst_closed _ _ _ (numericalSearch_closed hC),
      subst_closed _ _ _ numericalPairTerm_closed,
      subst_closed _ _ _ (numericalProjectionTerm_closed true),
      subst_closed _ _ _ (numericalProjectionTerm_closed false)] using
      Beta.contract 40 (app F (app (app numericalPairTerm
        (app (numericalSearch C) (app (numericalProjectionTerm true) (var 40))))
        (app (numericalProjectionTerm false) (var 40)))) (numeral n)
  have hp : Relation.ReflTransGen Beta (app (numericalProjectionTerm true) (numeral n))
      (numeral (Nat.pair b a)) := by
    simpa only [n,Nat.unpair_pair,ite_true] using numericalProjectionTerm_apply true n
  have hm : Relation.ReflTransGen Beta (app (numericalProjectionTerm false) (numeral n))
      (numeral m) := by
    simpa only [n,Nat.unpair_pair,Bool.false_eq_true,ite_false] using numericalProjectionTerm_apply false n
  exact (Relation.ReflTransGen.single hb).trans
    ((beta_steps_app_right F ((beta_steps_app
      (beta_steps_app_right numericalPairTerm ((beta_steps_app_right (numericalSearch C) hp).trans hS)) hm).trans
        (numericalPairTerm_apply c m))).trans hR)

/-- A single program works for all endpoints; no totality outside its path domain is asserted. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For a recursion through many stages, the upper endpoint must also be an input. Use the same total
    path checker $\Theta$, address accumulator $\LambdaTermName{addr}$, and zero-reversing term
    $\LambdaTermName{reject}$ as above, and put
    $$\begin{aligned}
    \LambdaTermName{findEnds}&:=\lambdaab{v}{\LambdaResultSearch\,
     (\lambdaab{k}{\LambdaTermName{reject}(\Theta(\LambdaNumericPair\,v\,k))})\,(\lambdaab{j}{j})},\\
    \LambdaTermName{readEnds}&:=\lambdaab{o}{\lambdaab{w}{
    o( \LambdaTermName{addr}( \LambdaNumericPair\,( \LambdaTermName{findEnds}( \LambdaNumericProjection{1}w))\,(
    \LambdaNumericProjection{2}w)))}}.
    \end{aligned}$$
    Thus $\LambdaTermName{findEnds}$ searches for a path with the two endpoints supplied as $v$. For input
    $w= \NatPair{ \NatPair{b}{a}}{m}$, the term $\LambdaTermName{readEnds}$ receives $\ChurchNumeral{w}$, computes
    the path, changes the address,
    and queries the supplied upper row once. No termination claim is made when a path does not exist.
-/
theorem exists_endpoint_reader :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q →
      ∀ b a, tableDomain q a → (∃ s, AccessPath b a s) → ∀ m,
        OracleRuns (tableRow q a) P (Nat.pair (Nat.pair b a) m) (tableRow q b m) := by
  classical
  obtain ⟨C,hC⟩ := exists_pathTest_program
  obtain ⟨F,f,hF,hf⟩ := exists_pathAddress_program
  have hQ := numericalIdentity_computes.uniform.query
  refine ⟨reindexProgram _ (pathQueryAddress C F),
    reindexProgram_closed hQ.1 (pathQueryAddress_closed hC.1 hF.1),?_⟩
  intro A q hq b a ha hp m
  have hex : ∃ c, pathTest (Nat.pair (Nat.pair b a) c) ≠ 0 := by
    obtain ⟨s,hs⟩ := hp
    refine ⟨NatListCode.encode s,?_⟩
    simp [pathTest,NatListCode.decode_encode,hs.state]
  let c := Nat.find hex
  have hc : AccessPath b a (NatListCode.decode c) := by
    have ht : pathTest (Nat.pair (Nat.pair b a) c) ≠ 0 := Nat.find_spec hex
    dsimp only [pathTest] at ht
    simp only [Nat.unpair_pair,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at ht
    exact (pathState_iff b a _).mp ht
  have hs := numericalSearch_hit hC (Nat.pair b a) c (Nat.find_spec hex)
    (fun k hk => not_ne_iff.mp (Nat.find_min hex hk))
  have hr := pathQueryAddress_apply hC.1 hF.1 b a m c _ hs (hF.2 (Nat.pair c m))
  have h := reindexProgram_runs hQ.1 (pathQueryAddress_closed hC.1 hF.1) (tableRow q a)
    (Nat.pair (Nat.pair b a) m) _ _ hr (hQ.2 (tableRow q a) _)
  simpa only [id_eq,Nat.unpair_pair,hf A q hq b a _ hc ha m] using h

def varyingReaderInput (U L : AlphaTerm) : AlphaTerm := pairNumerical
  (pairNumerical (numericalCompose L (pairNumerical (numericalProjectionTerm true)
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
    (numericalCompose U (numericalProjectionTerm true)))
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

theorem varyingReaderInput_computes {U L : AlphaTerm} {u l : ℕ → ℕ}
    (hU : NumericalComputes U u) (hL : NumericalComputes L l) :
    NumericalComputes (varyingReaderInput U L)
      (fun z => Nat.pair (Nat.pair (l (Nat.pair z.unpair.1 z.unpair.2.unpair.1))
        (u z.unpair.1)) z.unpair.2.unpair.2) := by
  have ha := projection_computes true
  have hn := (projection_computes true).comp (projection_computes false)
  have hm := (projection_computes false).comp (projection_computes false)
  exact ((hL.comp (ha.pair hn)).pair (hU.comp ha)).pair hm

def varyingReaderTemplate (P U L : AlphaTerm) : AlphaTerm :=
  reindexProgram P (varyingReaderInput U L)

theorem varyingReaderTemplate_subst (P U L C : AlphaTerm) (hP : P.Closed) (hC : C.Closed)
    (x : ℕ) (hx : 40 < x) :
    (varyingReaderTemplate P U L).subst x C =
      varyingReaderTemplate P (U.subst x C) (L.subst x C) := by
  have hc (i : ℕ) : i ∉ C.fv := by rw [hC]; simp
  have h1 : 1 ≠ x := by omega
  have h2 : 2 ≠ x := by omega
  have h40 : 40 ≠ x := by omega
  simp only [varyingReaderTemplate, varyingReaderInput, reindexProgram, pairNumerical,
    numericalCompose, numericalCombine,
    subst_lam_fresh _ _ 1 x h1 (hc 1), subst_lam_fresh _ _ 2 x h2 (hc 2),
    subst_lam_fresh _ _ 40 x h40 (hc 40), subst_app,
    subst_closed _ _ _ hP, subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_var, h1, h2, h40, ite_false]

/-- The upper- and lower-notation programs are numerical inputs to one compiler. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Computed jump-row reader indices
-/
theorem uniform_computed_reader_indices :
    ∃ I i, NumericalComputes I i ∧ ∀ e l,
      (Term.decode e).fv = ∅ → (Term.decode l).fv = ∅ → ∀ u g,
      NumericalComputes (Term.closedProgram e) u → NumericalComputes (Term.closedProgram l) g →
      ∀ a, (Term.decode (i (Nat.pair (Nat.pair e l) a))).fv = ∅ ∧
        ∀ (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q → tableDomain q (u a) →
          (∀ n, ∃ s, AccessPath (g (Nat.pair a n)) (u a) s) →
          Computes (tableRow q (u a)) (Term.closedProgram (i (Nat.pair (Nat.pair e l) a)))
            (fun z : ℕ => tableRow q (g (Nat.pair a z.unpair.1)) z.unpair.2) := by
  obtain ⟨P,hP,hp⟩ := exists_endpoint_reader
  obtain ⟨F,f,hF,hf⟩ := uniform_binary_template_indices
    (varyingReaderTemplate P (var 86) (var 87)) 86 87
  obtain ⟨S,s,hS,hs⟩ := uniform_pair_specialization_indices
  have hI := hS.comp ((hF.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨_,fun z => s (Nat.pair (f z.unpair.1) z.unpair.2),hI,
    fun e l he hl u g hU hL a => ?_⟩
  have he' : mk (Term.decode e) = Term.closedProgram e := (ite_eq_left he).symm
  have hl' : mk (Term.decode l) = Term.closedProgram l := (ite_eq_left hl).symm
  have ht := hf e l
  rw [he',hl',varyingReaderTemplate_subst _ _ _ _ hP hU.1 86 (by decide),
    varyingReaderTemplate_subst _ _ _ _ hP hL.1 87 (by decide)] at ht
  norm_num only [subst_var, ite_true, ite_false, subst_closed _ _ _ hU.1] at ht
  have hcode := varyingReaderInput_computes hU hL
  have hV := reindexProgram_closed hP hcode.1
  have hc : (Term.decode (f (Nat.pair e l))).fv = ∅ := by
    change (mk (Term.decode (f (Nat.pair e l)))).Closed
    rw [ht]
    exact hV
  have hprogram : Term.closedProgram (f (Nat.pair e l)) =
      varyingReaderTemplate P (Term.closedProgram e) (Term.closedProgram l) :=
    (ite_eq_left hc).trans ht
  obtain ⟨hclosed,hindex⟩ := hs (f (Nat.pair e l)) a hc
  rw [hprogram] at hindex
  simp only [Nat.unpair_pair]
  refine ⟨hclosed,fun A q hq hua hpath => ?_⟩
  rw [hindex]
  refine ⟨specializePairProgram_closed hV a,fun z => ?_⟩
  apply specializePairProgram_runs hV
  apply reindexProgram_runs hP hcode.1
  · exact hcode.2 (Nat.pair a z)
  · simpa only [Nat.unpair_pair, Encodable.encode_nat] using
      hp A q hq (g (Nat.pair a z.unpair.1)) (u a) hua (hpath z.unpair.1) z.unpair.2

/-- Specialization computes codes even for stages at which no path exists. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Computed jump-row reader indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Set $\LambdaTermName{upperProg}=P_e$ and $\LambdaTermName{lowerProg}=P_h$. Projections and numerical pairing
    give a closed total term $\LambdaTermName{readerInput}$ for the change of input
    $$\NatPair{a}{\NatPair{n}{m}}\longmapsto
      \NatPair{\NatPair{\ell(a,n)}{\upsilon(a)}}{m}.$$
    With the abbreviations expanded before abstraction, take
    $$\begin{aligned}
    \LambdaTermName{lowerInput}(w)&:= \LambdaTermName{lowerProg}( \LambdaNumericPair\,(
    \LambdaNumericProjection{1}w)\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))),\\
    \LambdaTermName{endpoints}(w)&:= \LambdaNumericPair\, \LambdaTermName{lowerInput}(w)\,(
    \LambdaTermName{upperProg}( \LambdaNumericProjection{1}w)),\\
    \LambdaTermName{readerInput}&:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{endpoints}(w)\,(
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}w))}.
    \end{aligned}$$
    Form the closed term
    $$\LambdaTermName{varyReader}:=\lambdaab{o}{\lambdaab{w}{\LambdaTermName{readEnds}o(\LambdaTermName{readerInput}w)}}$$
    and specialize its first numerical component:
    $$P_{\psi(e,h,a)}=\lambdaab{o}{\lambdaab{z}{\LambdaTermName{varyReader}o(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.$$
    To compute its code uniformly, first replace $\LambdaTermName{upperProg}, \LambdaTermName{lowerProg}$ by two
    fresh free variables in the expression for $\LambdaTermName{varyReader}$.
    Fix one named representative of that expression. The two-input substitution construction in
    §{sec:lambda-code-substitution} computes a code $\rho(e,h)$ of $\LambdaTermName{varyReader}$ from the supplied
    syntax codes.
    Now use the joint specialization map $\kappa$ from §{sec:lambda-pair-tree-programs} and put
    $$\psi(e,h,a):=\kappa(\rho(e,h),a).$$
    All fixed representatives are chosen before $e,h$ are supplied. Both code transformations terminate without
    running $\LambdaTermName{upperProg},\LambdaTermName{lowerProg},\LambdaTermName{varyReader}$ or searching for a path.

    For correctness, every trial of $\LambdaTermName{findEnds}$ terminates because $\Theta$ is total. An accepted
    path has a finite
    list code, so least-success search terminates at each required pair of endpoints. The address-accumulator
    identity then gives $G_{\upsilon(a)}(\mathcal A(c,m))=G_{\ell(a,n)}(m)$ for the selected code $c$.
    Two specialization contractions, pairing, and the computation of $\LambdaTermName{readerInput}$ reduce to that
    same reader run.
    Thus a single total code-producing term works for all stages, although the programs it produces need
    only terminate at stages satisfying the stated hypotheses.
    \end{proof}
-/
theorem computed_reader_indices {U G : AlphaTerm} {u g : ℕ → ℕ}
    (hU : NumericalComputes U u) (hG : NumericalComputes G g) :
    ∃ (I : AlphaTerm) (i : ℕ → ℕ), NumericalComputes I i ∧
      ∀ (a : ℕ) (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q → tableDomain q (u a) →
        (∀ n, ∃ s, AccessPath (g (Nat.pair a n)) (u a) s) →
        Computes (tableRow q (u a)) (Term.closedProgram (i a))
          (fun z : ℕ => tableRow q (g (Nat.pair a z.unpair.1)) z.unpair.2) := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep U
  obtain ⟨L,hL⟩ := Quotient.exists_rep G
  have ht : mk T = U := hT
  have hl : mk L = G := hL
  have htc : T.fv = ∅ := by
    have h := hU.1
    rw [← ht] at h
    exact h
  have hlc : L.fv = ∅ := by
    have h := hG.1
    rw [← hl] at h
    exact h
  have htp : Term.closedProgram T.code = U := by
    simpa only [Term.closedProgram,Term.decode_code,htc,ite_true] using ht
  have hlp : Term.closedProgram L.code = G := by
    simpa only [Term.closedProgram,Term.decode_code,hlc,ite_true] using hl
  obtain ⟨I,i,hI,hi⟩ := uniform_computed_reader_indices
  refine ⟨_,fun a => i (Nat.pair (Nat.pair T.code L.code) a),
    hI.comp ((numericalConstant_computes (Nat.pair T.code L.code)).pair numericalIdentity_computes),?_⟩
  intro a A q hq hua hpath
  exact (hi T.code L.code (by simpa only [Term.decode_code] using htc)
    (by simpa only [Term.decode_code] using hlc) u g
    (htp.symm ▸ hU) (hlp.symm ▸ hG) a).2 A q hq hua hpath


end KleeneNotation
end PolishSpaceBook
