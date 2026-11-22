module

public import PolishSpaceBook.LambdaCantorStagePrograms
public import PolishSpaceBook.LambdaRankJumpReaders
public import PolishSpaceBook.CantorDerivativeRecursion

@[expose] public section

/-! # Uniform decisions for transfinite Cantor--Bendixson tree stages

A total self-indexed compiler produces the stage programs before a base set
or tree is supplied. Well-founded induction verifies their execution.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative KleeneNotation
namespace CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

/-- Membership on all natural-word codes; nonbinary words are rejected. -/
def codedTree (T : Set (List Bool)) (n : ℕ) : Prop := Binary n ∧ decodeWord n ∈ T

def naturalTree (T : Set (List Bool)) : Set (List ℕ) :=
  {s | (∀ n ∈ s, n ≤ 1) ∧ s.map (fun n => decide (n = 1)) ∈ T}

theorem naturalTree_isSubtree {T : Set (List Bool)} (hT : IsSubtree T) :
    IsSubtree (naturalTree T) := by
  intro s t ht hst
  exact ⟨fun n hn => ht.1 n (hst.sublist.subset hn),hT ht.2 (hst.map _)⟩

@[simp] theorem binaryTree_naturalTree (T : Set (List Bool)) : binaryTree (naturalTree T) = T := by
  ext s
  have hb : ∀ n ∈ s.map Bool.toNat, n ≤ 1 := by
    simpa only [Binary,encodeWord,NatListCode.decode_encode] using binary_encodeWord s
  have he : (s.map Bool.toNat).map (fun n => decide (n = 1)) = s := by
    simpa only [decodeWord,encodeWord,NatListCode.decode_encode] using decodeWord_encodeWord s
  change ((∀ n ∈ s.map Bool.toNat, n ≤ 1) ∧ (s.map Bool.toNat).map (fun n => decide (n = 1)) ∈ T) ↔ s ∈ T
  rw [he]
  exact and_iff_right hb

theorem naturalTree_decode (T : Set (List Bool)) (n : ℕ) :
    NatListCode.decode n ∈ naturalTree T ↔ codedTree T n := Iff.rfl

theorem codedStage_eq {ι : Type*} (R : ι → ι → Prop) (hR : WellFounded R)
    (T : Set (List Bool)) (a : ι) (n : ℕ) :
    codedTree (stageTree R hR T a) n ↔
      codedTree T n ∧ ∀ b, R b a → codedTree (derivativeTree (stageTree R hR T b)) n := by
  rw [codedTree,stageTree_eq]
  constructor
  · rintro ⟨hn,ht,h⟩
    exact ⟨⟨hn,ht⟩,fun b hb => ⟨hn,h b hb⟩⟩
  · rintro ⟨⟨hn,ht⟩,h⟩
    exact ⟨hn,ht,fun b hb => (h b hb).2⟩

private theorem pure_bit_program {R : ℕ → Prop} (hR : DecidablePredicate (fun _ => 0) R) :
    ∃ P, NumericalComputes P (fun n => if R n then 1 else 0) := by
  obtain ⟨P,hP⟩ := hR
  have h : Computes (fun _ => 0) P (fun n : ℕ => if R n then 1 else 0) :=
    ⟨hP.1,fun n => by simpa only [Encodable.encode_nat] using hP.runs n⟩
  exact ⟨_,h.toNumerical (numericalConstant_computes 0)⟩

private theorem jump_value_congr (A : Set ℕ) {a b : ℕ} {ha : Valid a} {hb : Valid b}
    (h : a = b) : iteratedJump A a ha = iteratedJump A b hb := by
  subst b
  rfl

/-- Verification is separate from the numerical choice of all component indices. -/
theorem verify_stage_family (W : WellOrderPresentation (fun _ => 0))
    {P C D I : AlphaTerm} {d i g r : ℕ → ℕ} {q : ℕ}
    (hP : P.Closed)
    (hC : NumericalComputes C (fun z => if W.domain z.unpair.1 ∧ W.relation z.unpair.1 z.unpair.2 then 1 else 0))
    (hD : NumericalComputes D d) (hI : NumericalComputes I i)
    (hder : ∀ e ε (T : Set (List ℕ)), IsSubtree T →
      Decides ε (Term.closedProgram e) (fun n : ℕ => NatListCode.decode n ∈ T) →
      Decides (fourthJump ε) (Term.closedProgram (d e))
        (fun s : ℕ => Binary s ∧ decodeWord s ∈ derivativeTree (binaryTree T)))
    (hv : ∀ a : W.Carrier, Valid (g a.val))
    (hi : ∀ (a : W.Carrier) (A : Set ℕ),
      Computes (characteristic (iteratedJump A (g a.val) (hv a))) (Term.closedProgram (i a.val))
        (predecessorFiniteJumpRows W g hv A a 5))
    (hq : NumericalComputes (Term.closedProgram q) r)
    (hcompile : ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → Prop),
      Decides ε (specializePairProgram (specializePairProgram (stageMatrixProgram P C D I) q) a)
        (fun z : ℕ => M z.unpair.1 z.unpair.2) →
      Decides (jumpName ε) (Term.closedProgram (r a)) (fun n => ∀ b, M n b))
    (A : Set ℕ) (T : Set (List Bool)) (hT : IsSubtree T)
    (hPT : Decides (characteristic A) P (codedTree T)) (a₀ : W.Carrier) :
    Decides (jumpName (characteristic (iteratedJump A (g a₀.val) (hv a₀))))
      (Term.closedProgram (r a₀.val))
      (codedTree (stageTree W.order ((inferInstance : WellFounded W.order)) T a₀)) := by
  apply ((inferInstance : WellFounded W.order)).induction a₀
  intro a ih
  let U := stageTree W.order ((inferInstance : WellFounded W.order)) T
  let ε := characteristic (iteratedJump A (g a.val) (hv a))
  let L := fun b s => ∃ hb : W.domain b, codedTree (derivativeTree (U ⟨b,hb⟩)) s
  have hbase (k : ℕ) : OracleRuns ε (Term.closedProgram (i a.val)) (Nat.pair a.val k) (characteristic A k) := by
    have hn0 : ¬ W.order a a := irrefl a
    have hn : ¬ (W.domain a.val ∧ W.relation a.val a.val) := fun h => hn0 h.2
    have h := (hi a A).2 (Nat.pair a.val k)
    simpa only [predecessorFiniteJumpRows,Nat.unpair_pair,dite_eq_right hn,Encodable.encode_nat] using h
  have hm := stageMatrixProgram_decides (c := fun b a => W.domain b ∧ W.relation b a)
    hP (by
      refine ⟨hC.1,fun z => ?_⟩
      by_cases hz : W.domain z.unpair.1 ∧ W.relation z.unpair.1 z.unpair.2 <;>
        simpa [hz] using hC.2 z) hD.1 hI q a.val ε (codedTree T) L
    (fun s b => initialRunProgram_runs hP hI q a.val s b _ hbase (hPT.runs s)) (by
      intro s b hb
      let b' : W.Carrier := ⟨b,hb.1⟩
      let η := jumpName (characteristic (iteratedJump A (g b) (hv b')))
      have hlow : Decides η (Term.closedProgram (r b)) (fun n : ℕ => NatListCode.decode n ∈ naturalTree (U b')) := by
        simpa only [naturalTree_decode] using ih b' hb.2
      have hdd := hder (r b) η (naturalTree (U b'))
        (naturalTree_isSubtree (stageTree_isSubtree W.order ((inferInstance : WellFounded W.order)) T hT b')) hlow
      simp only [binaryTree_naturalTree] at hdd
      have hread (k : ℕ) : OracleRuns ε (Term.closedProgram (i a.val)) (Nat.pair b k) (fourthJump η k) := by
        have h := (hi a A).2 (Nat.pair b k)
        have hout : predecessorFiniteJumpRows W g hv A a 5 (Nat.pair b k) = fourthJump η k := by
          simp only [predecessorFiniteJumpRows,Nat.unpair_pair,dite_eq_left hb,finiteJumpName]
          apply congrArg (fun B : Set ℕ => fourthJump (jumpName (characteristic B)) k)
          exact jump_value_congr A (congrArg g (congrArg Prod.fst (Nat.unpair_pair b k)))
        simpa only [Encodable.encode_nat,hout] using h
      have he : L b s ↔ codedTree (derivativeTree (U b')) s := by
        constructor
        · rintro ⟨hb',h⟩; exact h
        · intro h; exact ⟨hb.1,h⟩
      have hh := derivativeRunProgram_runs hD hI hq a.val s b _ hread (hdd.runs s)
      simpa only [he,codedTree] using hh)
  have hs := hcompile a.val ε (fun s b => codedTree T s ∧ (W.domain b ∧ W.relation b a.val → L b s)) hm
  convert hs using 1
  funext s
  apply propext
  rw [codedStage_eq]
  constructor
  · intro h b
    exact ⟨h.1,fun hb => ⟨hb.1,h.2 ⟨b,hb.1⟩ hb.2⟩⟩
  · intro h
    refine ⟨(h 0).1,fun b hb => ?_⟩
    obtain ⟨hd,hv⟩ := (h b.val).2 ⟨b.property,hb⟩
    exact hv

/-- The indices are total everywhere; correctness is asserted along the presented well order. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Uniform Cantor--Bendixson stage decisions
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the computed readers with five successive jumps and put
    $$\varepsilon_a:=\chi_{\IteratedJump{A}{g(a)}}.$$
    At this input, the reader with index $\CantorReaderIndex{a}$ supplies five jumps of $\varepsilon_b$ on row $b$
    when $b\in D$ and $bRa$, and supplies $\chi_A$ otherwise. In particular, row $a$ supplies the
    original input, since $R$ is irreflexive. Write $\delta$ for the derivative-index transformation
    proved above. §{sec:lambda-cantor-derivative-programs} constructs one closed template $M$
    which, given $\NatPair{k}{\NatPair{a}{\NatPair{\LambdaListCode{s}}{b}}}$, tests initial-tree membership using row $a$,
    then tests the predecessor condition. Only for a genuine predecessor does it compute $P_k(b)$,
    apply $\delta$ to that index, and run the resulting derivative program using row $b$.

    Let $z$ be the syntax code of a fixed named representative of $M$, and write $\LambdaTwoParameterIndex{z}{k}{a}$ for the
    syntax code of its two specializations. The uniform self-indexed universal-family construction in
    §{sec:lambda-rank-decision-programs} computes the self-index $q(z)$ uniformly from $z$. Put
    $$r(a):=\upsilon(\LambdaTwoParameterIndex{z}{q(z)}{a}).$$
    The program $P_{q(z)}$ computes this function at every numerical stage. Both the self-index and the stage indices
    are obtained from the supplied template code using only numerical syntax operations and the universal-quantifier
    transformation. No stage program is executed. Thus the indices are available before their correctness is proved.

    We prove correctness by well-founded induction on $a$. For a predecessor $b$, the induction
    hypothesis gives the tree decider at $\varepsilon_b'$. The derivative compiler needs four more jumps,
    so row $b$ supplies exactly its required input. The guarded template therefore decides
    $$s\in T\ \land\ \bigl(b\in D\land bRa\Longrightarrow
     s\in\ClosedTreeCode{\cbderivative{\TreeBody{T_b}}}\bigr)$$
    at $\varepsilon_a$. The universal-quantifier compiler decides its universal closure in $b$ at
    $\varepsilon_a'$. By the tree recursion, this is precisely membership in $T_a$. If there are no
    predecessors, the guarded part always returns one and the result is the initial-tree test.
    Nonbinary word codes are rejected by that test at every stage.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For transfinite computation, use $G=\{b\in D:bRa\}$ at stage $a$. The preceding lemma requires a
    joint decider for the predecessor derivative trees. We now construct its program indices and
    supply its lower inputs from a common iterated jump. No test for limit stages or choice of cofinal
    sequences is needed.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Effectively, the safe jump-by-stage conclusion requires both a recursive ordinal bound and compact finite branching.
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
theorem recursive_cantor_stage_deciders (W : WellOrderPresentation (fun _ => 0))
    (P : AlphaTerm) (hP : P.Closed) :
    ∃ (G Q : AlphaTerm) (g r : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes Q r ∧
      ∃ hv : ∀ a : W.Carrier, Valid (g a.val), ∀ (A : Set ℕ) (T : Set (List Bool)),
        IsSubtree T → Decides (characteristic A) P (codedTree T) → ∀ a : W.Carrier,
          Decides (jumpName (characteristic (iteratedJump A (g a.val) (hv a))))
            (Term.closedProgram (r a.val))
            (codedTree (stageTree W.order ((inferInstance : WellFounded W.order)) T a)) := by
  have hd := W.domain_decidable.precompNumerical (projection_computes true)
    (g := fun z : ℕ => z.unpair.1) (by simp)
  have hr := W.relation_decidable.precompNumerical numericalIdentity_computes
    (g := fun z : ℕ => (z.unpair.1,z.unpair.2)) (fun z => (Nat.pair_unpair z).symm)
  obtain ⟨C,hC⟩ := pure_bit_program (hd.and hr)
  obtain ⟨D,d,hD,hder⟩ := derivative_index_transform
  obtain ⟨G,I,g,i,hG,hI,hv,hi⟩ := recursive_order_finiteJump_readers W 5
  have hM := stageMatrixProgram_closed hP hC hD.1 hI
  obtain ⟨q,r,hq,hcompile⟩ := universally_quantified_self_family (stageMatrixProgram P C D I) hM
  refine ⟨G,Term.closedProgram q,g,r,hG,hq,hv,fun A T hT hPT a₀ => ?_⟩
  exact verify_stage_family W hP (by
    refine ⟨hC.1,fun z => ?_⟩
    by_cases hz : W.domain z.unpair.1 ∧ W.relation z.unpair.1 z.unpair.2 <;>
      simpa [hz] using hC.2 z) hD hI hder hv hi hq hcompile A T hT hPT a₀

/-- All presentation- and tree-dependent choices are numerical inputs to fixed compilers. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Cantor stage indices from decision programs
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Take $\CantorNotationIndex{d}{t}$ and the joint reader-index map from the uniform reader construction.
    §{sec:lambda-cantor-derivative-programs} gives the predecessor-test index $\kappa(d,t)$ and the index
    $\iota(d,t)$ of the numerical function producing five-jump readers. Fix the derivative compiler once.
    The stage-template generators from that section now give
    $$\begin{aligned}
    \CantorSelfIndex{d}{t}{p}&:=q_0\bigl(p,\kappa(d,t),\iota(d,t)\bigr),\\
    \CantorStageIndex{d}{t}{p}{a}&:=r_0\bigl(p,\kappa(d,t),\iota(d,t),a\bigr).
    \end{aligned}$$
    Composition proves totality of these maps and the claimed computation by the self-indexed program.
    Under the decision hypotheses, the generated predecessor test and reader-index program satisfy exactly the
    hypotheses used in the preceding well-founded induction. The matrix compiler produces that same guarded
    stage program and the self-indexed universal compiler gives the same one-jump closure. Apply the preceding
    induction with these generated components. It proves the stage decision for every starting set and initial
    tree, while preserving the original tree program and all numerical parameters.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the five-jump reader, fix a named representative of the joint reader-index program from
    §{sec:edst-borel-rank-layers}, with code $h$. It receives $\NatPair{\NatPair{d}{t}}{\NatPair{k}{a}}$.
    Two numerical parameter insertions give
    $$\iota(d,t):=p\bigl(p(h,\NatPair{d}{t}),5\bigr).$$
    The program $P_{\iota(d,t)}$ computes $a\mapsto i(d,t,5,a)$ on every natural-number input, for every pair $d,t$.
    The decision and well-order hypotheses are needed for the reader's interpretation, not for this index computation.
-/
theorem uniform_cantor_stage_deciders :
    ∃ (E Q R : AlphaTerm) (e q g r : ℕ → ℕ),
      NumericalComputes E e ∧ NumericalComputes Q q ∧ NumericalComputes R r ∧
      (∀ z, (Term.decode (e z)).fv = ∅ ∧
        NumericalComputes (Term.closedProgram (e z)) (fun a => g (Nat.pair z a))) ∧
      (∀ z, NumericalComputes (Term.closedProgram (q z)) (fun a => r (Nat.pair z a))) ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d t p,
        (Term.decode d).fv = ∅ → (Term.decode t).fv = ∅ → (Term.decode p).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram t)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∃ hv : ∀ a : W.Carrier, Valid (g (Nat.pair (Nat.pair d t) a.val)),
          ∀ (A : Set ℕ) (T : Set (List Bool)), IsSubtree T →
            Decides (characteristic A) (Term.closedProgram p) (codedTree T) → ∀ a : W.Carrier,
              Decides (jumpName (characteristic (iteratedJump A (g (Nat.pair (Nat.pair d t) a.val)) (hv a))))
                (Term.closedProgram (r (Nat.pair (Nat.pair (Nat.pair d t) p) a.val)))
                (codedTree (stageTree W.order ((inferInstance : WellFounded W.order)) T a)) := by
  obtain ⟨E,I,e,i,g,hE,hI,he,hread⟩ := uniform_order_finiteJump_readers
  obtain ⟨T₀,hT₀⟩ := Quotient.exists_rep I
  have ht₀ : mk T₀ = I := hT₀
  have hc₀ : T₀.fv = ∅ := by
    have h := hI.1
    rw [← ht₀] at h
    exact h
  have hp₀ : Term.closedProgram T₀.code = I := by
    simpa only [Term.closedProgram,Term.decode_code,hc₀,ite_true] using ht₀
  obtain ⟨S,s,hS,hs⟩ := uniform_numerical_parameter_indices
  let v (z : ℕ) := s (Nat.pair (s (Nat.pair T₀.code z)) 5)
  have hV := hS.comp ((hS.comp ((numericalConstant_computes T₀.code).pair
    numericalIdentity_computes)).pair (numericalConstant_computes 5))
  have hvprog (z : ℕ) : (Term.decode (v z)).fv = ∅ ∧
      NumericalComputes (Term.closedProgram (v z)) (fun a => i (Nat.pair z (Nat.pair 5 a))) := by
    obtain ⟨hc,_,h⟩ := hs T₀.code z (by simpa only [Term.decode_code] using hc₀)
    have hi₁ := h i (by rw [hp₀]; exact hI)
    obtain ⟨hc',_,h'⟩ := hs (s (Nat.pair T₀.code z)) 5 hc
    exact ⟨hc',h' _ hi₁⟩
  obtain ⟨C,c,hC,hc⟩ := uniform_predecessor_test_indices
  obtain ⟨D,δ,hD,hder⟩ := derivative_index_transform
  obtain ⟨Qₘ,Rₘ,qₘ,rₘ,hQₘ,hRₘ,hself,hm⟩ := uniform_stage_index_families D hD.1
  let w (z : ℕ) := Nat.pair (Nat.pair z.unpair.2 (c z.unpair.1)) (v z.unpair.1)
  have hW := ((projection_computes false).pair (hC.comp (projection_computes true))).pair
    (hV.comp (projection_computes true))
  let q (z : ℕ) := qₘ (w z)
  let r (z : ℕ) := rₘ (Nat.pair (w z.unpair.1) z.unpair.2)
  have hQ := hQₘ.comp hW
  have hR := hRₘ.comp ((hW.comp (projection_computes true)).pair (projection_computes false))
  have hqall (z : ℕ) : NumericalComputes (Term.closedProgram (q z)) (fun a => r (Nat.pair z a)) := by
    simpa only [q,r,Nat.unpair_pair] using hself (w z)
  refine ⟨E,_,_,e,q,g,r,hE,hQ,hR,he,hqall,fun W d t p hd ht hp hDom hRel => ?_⟩
  obtain ⟨hcv,hguard⟩ := hc W d t hd ht hDom hRel
  obtain ⟨hv,hrd⟩ := hread W d t hd ht hDom hRel
  refine ⟨hv,fun A T hT hPT a => ?_⟩
  let z := Nat.pair (Nat.pair d t) p
  have hcompile (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → Prop)
      (hdm : Decides ε (specializePairProgram (specializePairProgram
        (stageMatrixProgram (Term.closedProgram p) (Term.closedProgram (c (Nat.pair d t))) D
          (Term.closedProgram (v (Nat.pair d t)))) (q z)) a)
        (fun n : ℕ => M n.unpair.1 n.unpair.2)) :
      Decides (jumpName ε) (Term.closedProgram (r (Nat.pair z a))) (fun n => ∀ b, M n b) := by
    have h := hm p (c (Nat.pair d t)) (v (Nat.pair d t)) hp hcv (hvprog _).1 _ _
      hguard (hvprog _).2 a ε M (by simpa only [q,z,w,Nat.unpair_pair] using hdm)
    simpa only [r,z,w,Nat.unpair_pair] using h
  exact verify_stage_family W (g := fun b => g (Nat.pair (Nat.pair d t) b))
    (Term.closedProgram_closed p) hguard hD (hvprog _).2 hder hv
    (fun a A => hrd 5 a A) (hqall z) hcompile A T hT hPT a

end CantorDerivative
end PolishSpaceBook
