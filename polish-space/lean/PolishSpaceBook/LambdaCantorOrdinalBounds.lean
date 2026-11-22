module

public import PolishSpaceBook.LambdaCantorBorelCodes
public import PolishSpaceBook.LambdaNotationBounds

@[expose] public section

/-! # A specified Cantor--Bendixson stage above a notation bound

The root of the certified descent tree has a computable, constant node code.
Its position in Kleene--Brouwer order bounds the value of the notation. Stage
trees depend only on ordinal position, so a stable earlier stage remains stable
at this root; finding the first stable stage is unnecessary.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace CantorDerivative
local instance : Encodable (List ℕ) := NatListCode.encodable
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable def ordinalStageTree (T : Set (List Bool)) (α : Ordinal) : Set (List Bool) :=
  stageTree (fun a b : Ordinal => a < b) Ordinal.lt_wf T α

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The stage tree depends only on ordinal position. To see this, compare the recursion on a well
    order with the same recursion indexed by ordinals. Induct on the position of the current element.
    Its predecessors occur at exactly the smaller ordinal positions, each once. The induction
    hypothesis identifies the earlier stage trees, so the derivative factors and their intersection
    are identical. In particular the bodies agree. If a stage at position $\alpha$ is stable, the
    persistence result gives the same body at every position at least $\alpha$. Apply this with
    $$\alpha\le\KleeneValue{a}\le\rho_{W_a}(0).$$
    This selects the root stage without searching for the first stable stage.
    \end{proof}
-/
theorem stageTree_eq_ordinalStage {ι : Type} (R : ι → ι → Prop) [IsWellOrder ι R]
    (T : Set (List Bool)) (a : ι) :
    stageTree R ((inferInstance : WellFounded R)) T a = ordinalStageTree T (Ordinal.typein R a) := by
  induction a using ((inferInstance : WellFounded R)).induction with
  | h a ih =>
    rw [stageTree_eq]
    unfold ordinalStageTree
    rw [stageTree_eq]
    ext s
    simp only [mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨ht,h⟩
      refine ⟨ht,fun β hβ => ?_⟩
      obtain ⟨b,hb⟩ := Ordinal.typein_surj R (hβ.trans (Ordinal.typein_lt_type R a))
      have hba : R b a := (Ordinal.typein_lt_typein R).mp (hb ▸ hβ)
      simpa only [ih b hba,ordinalStageTree,hb] using h b hba
    · rintro ⟨ht,h⟩
      refine ⟨ht,fun b hb => ?_⟩
      simpa only [ih b hb,ordinalStageTree] using h (Ordinal.typein R b) ((Ordinal.typein_lt_typein R).mpr hb)

theorem ordinalStage_stable_later (T : Set (List Bool)) {α β : Ordinal} (hab : α ≤ β)
    (ha : treeBody (ordinalStageTree T α) = derivedSet (treeBody (ordinalStageTree T α))) :
    treeBody (ordinalStageTree T β) = treeBody (ordinalStageTree T α) := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact stable_stage_persists (fun a b : Ordinal => a < b) Ordinal.lt_wf T h ha

/-- One total domain test receives both the starting notation and the word code. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The starting notation can itself be a numerical input. Let $z= \NatPair{a}{e}$, and let a trial receive $v=
    \NatPair{z}{j}$. Using the certificate tester $\LambdaTermName{cert}$
    just constructed, put
    $$\begin{aligned}
    \LambdaTermName{seedAll}(z)&:= \LambdaListCons\,( \LambdaNumericPair\,( \LambdaNumericProjection{1}z)\,
    \ChurchNumeral{0})\,( \LambdaNumericProjection{2}z),\\
    \LambdaTermName{entryAll}(v)&:= \LambdaListGet\,( \LambdaNumericPair\,( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{1}v))\,( \LambdaNumericProjection{2}v)),\\
    \LambdaTermName{prevAll}(v)&:= \LambdaNumericProjection{1} \bigl( \LambdaListGet\,( \LambdaNumericPair\,
    \LambdaTermName{seedAll}( \LambdaNumericProjection{1}v)\,( \LambdaNumericProjection{2}v)) \bigr),\\
    \LambdaTermName{trialAll}&:= \lambdaab{v}{ \LambdaTermName{cert}( \LambdaNumericPair\,
    \LambdaTermName{prevAll}(v)\, \LambdaTermName{entryAll}(v))},\\
     \LambdaTermName{descAll}&:=\lambdaab{z}{\LambdaBoundedProduct{\LambdaTermName{trialAll}}
       (\LambdaNumericPair\,z\,(\LambdaListLength\,(\LambdaNumericProjection{2}z)))}.
    \end{aligned}$$
    Expand the abbreviations with fresh binders. The closed term $\LambdaTermName{descAll}$ decides whether the word coded
    by $e$ belongs to the certified descent tree starting at $a$, jointly for all numerical inputs.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The dummy initial entry stores the starting notation. At trial $j$, the projections and list access
    supply the preceding notation and the next certified entry. The certificate test returns the
    correct edge bit, and the bounded product checks every entry of the supplied word. Its value on
    the empty word is one. All numerical subcomputations terminate for every starting number, so no
    notation-validity test is needed. Restricting the starting number to a valid notation is used only
    in the separate proof that the resulting Kleene--Brouwer order is well founded.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    §{sec:lambda-certified-descent} gives the finite certificate test and the joint domain
    program. It tests only finitely many certificates on each input, even when the starting number
    is not a valid notation. Validity is used to prove that the descent tree is well founded, not to
    run its domain test. The empty word always belongs to the tree and has code zero.
-/
theorem notation_domain_joint_decidable :
    DecidablePredicate (fun _ => 0) (fun z : ℕ =>
      NatListCode.decode z.unpair.2 ∈ CertifiedDescent.nodes KleeneNotation.edgeCertificate z.unpair.1) := by
  have hz := projection_computes true
  have hi := projection_computes false
  have ha := (projection_computes true).comp hz
  have he := (projection_computes false).comp hz
  have hcons := successor_computes.comp ((ha.pair (numericalConstant_computes 0)).pair he)
  have hp := (projection_computes true).comp (listGet_computes.comp (hcons.pair hi))
  have hc := listGet_computes.comp (he.pair hi)
  let f := fun v : ℕ => Nat.pair
    ((NatListCode.decode (Nat.pair (Nat.pair v.unpair.1.unpair.1 0) v.unpair.1.unpair.2 + 1)).getD v.unpair.2 0).unpair.1
    ((NatListCode.decode v.unpair.1.unpair.2).getD v.unpair.2 0)
  have hpair := hp.pair hc
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.succ_eq_add_one,Nat.unpair_pair] at hpair
  change NumericalComputes _ f at hpair
  have ht := (KleeneNotation.edgeCertificate_decidable (fun _ => 0)).precompNumerical
    (g := f) hpair (fun _ => rfl)
  have hall := ht.boundedAll (listLength_computes.comp (projection_computes false))
  have hd (a e : ℕ) : NatListCode.decode (Nat.pair (Nat.pair a 0) e + 1) =
      Nat.pair a 0 :: NatListCode.decode e := by
    simpa only [NatListCode.encode,NatListCode.encode_decode] using
      NatListCode.decode_encode (Nat.pair a 0 :: NatListCode.decode e)
  simpa only [f,Encodable.encode_nat,Bool.false_eq_true,ite_true,ite_false,Nat.succ_eq_add_one,hd,
    Nat.unpair_pair,CertifiedDescent.nodes_iff] using hall

noncomputable def notationOrder (a : ℕ) (ha : KleeneNotation.Valid a) : WellOrderPresentation (fun _ => 0) :=
  KleeneBrouwer.presentation
    (CertifiedDescent.tree KleeneNotation.edgeCertificate (KleeneNotation.edgeCertificate_decidable (fun _ => 0)) a)
    (CertifiedDescent.wellFounded KleeneNotation.edgeCertificate KleeneNotation.edgeCertificate_sound ha.acc)

noncomputable def notationRoot (a : ℕ) (ha : KleeneNotation.Valid a) : (notationOrder a ha).Carrier :=
  ⟨0,by change NatListCode.decode 0 ∈ CertifiedDescent.nodes KleeneNotation.edgeCertificate a
        simpa only [NatListCode.decode] using CertifiedDescent.root_mem KleeneNotation.edgeCertificate a⟩

section UniformPresentation
attribute [local instance] Classical.propDecidable

/-- The domain-program code varies with the notation; the comparison-program code is fixed. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform notation presentation indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Fix a named representative of the joint numerical domain tester above, with syntax code $u$,
    and a named representative of the numerical Kleene--Brouwer comparison term, with syntax code $t$. Write
    $\sigma(u,a)$ for the numerical parameter-index map of §{sec:lambda-index-recursion}, and put
    $$\DescentDomainIndex{a}:=\sigma(u,a).$$
    Parameter insertion gives a closed program that computes the joint domain test with its first
    argument fixed at $a$. The comparison term is independent of the tree. Both representatives
    are fixed before any starting number is supplied. The generated domain program terminates on
    every node code, even for an invalid notation; validity is needed only for well-foundedness.
-/
theorem uniform_notation_presentation_indices :
    ∃ (D : AlphaTerm) (d : ℕ → ℕ) (t : ℕ), NumericalComputes D d ∧
      (Term.decode t).fv = ∅ ∧ ∀ a, (Term.decode (d a)).fv = ∅ ∧
        ∀ ha : KleeneNotation.Valid a,
          NumericalComputes (Term.closedProgram (d a))
            (fun n => if (notationOrder a ha).domain n then 1 else 0) ∧
          NumericalComputes (Term.closedProgram t)
            (fun z => if (notationOrder a ha).relation z.unpair.1 z.unpair.2 then 1 else 0) := by
  obtain ⟨P,hP⟩ := notation_domain_joint_decidable
  have hp : Computes (fun _ => 0) P (fun z : ℕ =>
      if NatListCode.decode z.unpair.2 ∈ CertifiedDescent.nodes KleeneNotation.edgeCertificate z.unpair.1
      then 1 else 0) := ⟨hP.1,fun z => by simpa only [Encodable.encode_nat] using hP.runs z⟩
  have hN := hp.toNumerical (numericalConstant_computes 0)
  obtain ⟨T,hT⟩ := Quotient.exists_rep (app P (numericalConstant 0))
  have ht : mk T = _ := hT
  have hc : T.fv = ∅ := by
    have h := hN.1
    rw [← ht] at h
    exact h
  have hprogram : Term.closedProgram T.code = app P (numericalConstant 0) := by
    simpa only [Term.closedProgram,Term.decode_code,hc,ite_true] using ht
  obtain ⟨S,s,hS,hs⟩ := uniform_numerical_parameter_indices
  have hD := hS.comp ((numericalConstant_computes T.code).pair numericalIdentity_computes)
  obtain ⟨U,hU⟩ := Quotient.exists_rep (uncurryNumerical KleeneBrouwer.compareTerm)
  have hu : mk U = _ := hU
  have huc : U.fv = ∅ := by
    have h := KleeneBrouwer.compare_computes.1
    rw [← hu] at h
    exact h
  have hup : Term.closedProgram U.code = uncurryNumerical KleeneBrouwer.compareTerm := by
    simpa only [Term.closedProgram,Term.decode_code,huc,ite_true] using hu
  refine ⟨_,fun a => s (Nat.pair T.code a),U.code,hD,
    by simpa only [Term.decode_code] using huc,fun a => ?_⟩
  obtain ⟨hcl,_,h⟩ := hs T.code a (by simpa only [Term.decode_code] using hc)
  have hn := h _ (by rw [hprogram]; exact hN)
  refine ⟨hcl,fun ha => ⟨?_,?_⟩⟩
  · refine ⟨hn.1,fun n => ?_⟩
    by_cases hn' : NatListCode.decode n ∈ CertifiedDescent.nodes KleeneNotation.edgeCertificate a <;>
      simpa [Nat.unpair_pair,notationOrder,KleeneBrouwer.presentation,CertifiedDescent.tree,hn'] using hn.2 n
  · rw [hup]
    refine ⟨KleeneBrouwer.compare_computes.1,fun z => ?_⟩
    by_cases hz : KleeneBrouwer.Before (NatListCode.decode z.unpair.1) (NatListCode.decode z.unpair.2) <;>
      simpa [notationOrder,KleeneBrouwer.presentation,KleeneBrouwer.bit,hz] using
        KleeneBrouwer.compare_computes.2 z

/-- Notation and initial-tree indices are inputs, not parameters chosen before compilation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Root stage indices from ordinal notations
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Use the total map $\DescentDomainIndex{a}$ and the fixed comparison index $t$ from §{sec:lambda-certified-descent}.
    Let $\CantorNotationIndex{d}{t}$ and $\CantorStageIndex{d}{t}{p}{a}$ be the preceding stage generators, and let
    $P_{\CantorNotationIndex{d}{t}}$ compute
    $g_{d,t}$. Define
    $$\begin{aligned}
    \nu(a)&:=g_{\DescentDomainIndex{a},t}(0),\\
    h(a,p)&:=\CantorStageIndex{\DescentDomainIndex{a}}{t}{p}{0}.
    \end{aligned}$$
    The second map is a composition of total numerical maps. For the first, compute the index
    $\CantorNotationIndex{\DescentDomainIndex{a}}{t}$ and run the universal numerical evaluator at input $0$. This
    terminates for every
    $a$, because the stage generator produces a total numerical program for every pair of input
    indices. Thus both maps are total before any validity assumption is imposed. For a valid notation,
    the domain and comparison programs present $W_a$. Apply the stage-decision theorem to this
    presentation at its root, whose node code is $0$, and use the preceding stable-stage comparison.
-/
theorem uniform_notation_root_stage_deciders :
    ∃ (B H : AlphaTerm) (b h : ℕ → ℕ),
      NumericalComputes B b ∧ NumericalComputes H h ∧
      ∀ a (ha : KleeneNotation.Valid a), ∃ hb : KleeneNotation.Valid (b a),
        ∀ p, (Term.decode p).fv = ∅ → ∀ (A : Set ℕ) (T : Set (List Bool)),
          IsSubtree T → Decides (characteristic A) (Term.closedProgram p) (codedTree T) →
          Decides (jumpName (characteristic (KleeneNotation.iteratedJump A (b a) hb)))
            (Term.closedProgram (h (Nat.pair a p)))
            (codedTree (stageTree (notationOrder a ha).order
              ((inferInstance : WellFounded (notationOrder a ha).order)) T (notationRoot a ha))) := by
  obtain ⟨D,d,t,hD,ht,hd⟩ := uniform_notation_presentation_indices
  obtain ⟨E,Q,R,e,q,g,r,hE,hQ,hR,he,hq,hr⟩ := uniform_cantor_stage_deciders
  have hG := hE.evaluateFamily (fun z => (he z).2)
  have hB := hG.comp ((hD.pair (numericalConstant_computes t)).pair
    (numericalConstant_computes 0))
  have hH := hR.comp ((((hD.comp (projection_computes true)).pair
    (numericalConstant_computes t)).pair (projection_computes false)).pair
      (numericalConstant_computes 0))
  let b := fun a => g (Nat.pair (Nat.pair (d a) t) 0)
  let h := fun z : ℕ => r (Nat.pair (Nat.pair (Nat.pair (d z.unpair.1) t) z.unpair.2) 0)
  simp only [Nat.unpair_pair] at hB
  refine ⟨_,_,b,h,hB,hH,fun a ha => ?_⟩
  have hdc := (hd a).1
  obtain ⟨hdom,hrel⟩ := (hd a).2 ha
  obtain ⟨hv,_⟩ := hr (notationOrder a ha) (d a) t (Term.churchNumeral 0).code hdc ht
    (by simp only [Term.decode_code,Term.churchNumeral_closed]) hdom hrel
  refine ⟨hv (notationRoot a ha),fun p hp A T hT hPT => ?_⟩
  obtain ⟨hv',hout⟩ := hr (notationOrder a ha) (d a) t p hdc ht hp hdom hrel
  simpa only [b,h,Nat.unpair_pair,notationRoot] using hout A T hT hPT (notationRoot a ha)

end UniformPresentation

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Every candidate predecessor has a certificate. The descent-rank comparison therefore bounds
    $\KleeneValue{a}$ by the strict-extension rank of the root. Every proper extension precedes its
    prefix in Kleene--Brouwer order. Induction on strict extension bounds each node's rank by its
    position in that order, giving the displayed inequality at the root.
-/
theorem value_le_notationRoot_position (a : ℕ) (ha : KleeneNotation.Valid a) :
    KleeneNotation.value a ha ≤ Ordinal.typein (notationOrder a ha).order (notationRoot a ha) := by
  let C := KleeneNotation.edgeCertificate
  let T := CertifiedDescent.tree C (KleeneNotation.edgeCertificate_decidable (fun _ => 0)) a
  let hw := CertifiedDescent.wellFounded C KleeneNotation.edgeCertificate_sound ha.acc
  let root : T.tree := ⟨[],CertifiedDescent.root_mem C a⟩
  have hr := CertifiedDescent.rank_le C KleeneNotation.edgeCertificate_complete hw ha.acc root
    (CertifiedDescent.endpoint_nil a)
  let : WellFounded (strictTreeExtension T.tree) := hw
  have hp := wellFoundedRank_le_of_relation_preserving
    (r := strictTreeExtension T.tree) (s := (notationOrder a ha).order)
    (KleeneBrouwer.presentationIso T hw)
    (fun _ _ h => (KleeneBrouwer.presentationIso T hw).map_rel_iff.mpr (KleeneBrouwer.extension_before h)) root
  rw [WellFounded.rank_eq_typein (notationOrder a ha).order] at hp
  exact hr.trans hp

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: A specified stage above a notation bound
-/
theorem notationRoot_stage_eq_stable (a : ℕ) (ha : KleeneNotation.Valid a)
    (T : Set (List Bool)) {α : Ordinal} (hα : α ≤ KleeneNotation.value a ha)
    (hs : treeBody (ordinalStageTree T α) = derivedSet (treeBody (ordinalStageTree T α))) :
    treeBody (stageTree (notationOrder a ha).order ((inferInstance : WellFounded (notationOrder a ha).order))
      T (notationRoot a ha)) = treeBody (ordinalStageTree T α) := by
  rw [stageTree_eq_ordinalStage]
  exact ordinalStage_stable_later T (hα.trans (value_le_notationRoot_position a ha)) hs

/-- Total numerical compilers preserve both the notation and initial-tree program as inputs. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Uniform codes at a notation bound
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Bounded effective Cantor--Bendixson
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Take the total maps $\nu(a),h(a,p)$ from the root-stage corollary and the label-index constructions
    from §{sec:lambda-cantor-derivative-programs}. Write $f(e)$ for the tree-body label index,
    $\TreeDifferenceLabelIndex{e}{j}$ for the tree-difference label index, and
    $\PureTreeProgramIndex{p}$ for the index of the initial-tree program with its input function ignored. Put
    $$\begin{aligned}
    \CantorKernelLabelIndex{a}{p}&:=f\bigl(h(a,p)\bigr),\\
    \CantorScatteredLabelIndex{a}{p}&:=\TreeDifferenceLabelIndex{\PureTreeProgramIndex{p}}{h(a,p)}.
    \end{aligned}$$
    Composition proves totality. Under the hypotheses, the root-stage program decides a tree whose
    body is the stable body. The closed-tree recursion theorem identifies it as the greatest perfect
    subset of the initial body. The first label compiler gives the Borel code of this tree body.
    The program with index $\PureTreeProgramIndex{p}$ decides the initial tree at the same parameter, so the second label
    compiler gives the difference between the initial body and that perfect kernel. Both label maps
    use exactly the input function used by the root-stage decider.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Let $a$ be the supplied notation and $p$ the index of the initial-tree decider. The root-stage
    corollary computes $\nu(a)$ and $h(a,p)$; the tree decided by $P_{h(a,p)}$ has the stable body,
    hence is a closed-tree code for the perfect kernel. The preceding corollary computes $\CantorKernelLabelIndex{a}{p}$
    and $\CantorScatteredLabelIndex{a}{p}$ for the two Borel label maps. All three generated programs use the same parameter
    $\chi_{(\IteratedJump{\emptyset}{\nu(a)})'}$, which is hyperarithmetic because $\nu(a)\in\KleeneO$.
    No search for the first stable stage is used. The ordinal level of the parameter need not be
    $\alpha+1$.
-/
theorem uniform_bounded_notation_borel_codes :
    ∃ (B H L D : AlphaTerm) (b h l d : ℕ → ℕ),
      NumericalComputes B b ∧ NumericalComputes H h ∧ NumericalComputes L l ∧ NumericalComputes D d ∧
      ∀ a (ha : KleeneNotation.Valid a), ∃ hb : KleeneNotation.Valid (b a),
        ∀ p, (Term.decode p).fv = ∅ →
        ∀ T : Set (List Bool), IsSubtree T → Decides (fun _ => 0) (Term.closedProgram p) (codedTree T) →
          (∃ α : Ordinal, α ≤ KleeneNotation.value a ha ∧
            treeBody (ordinalStageTree T α) = derivedSet (treeBody (ordinalStageTree T α))) →
          ∃ (V : Set (List Bool)) (K S : BorelExpression.Code),
            IsSubtree V ∧
            Decides (jumpName (characteristic (KleeneNotation.iteratedJump ∅ (b a) hb)))
              (Term.closedProgram (h (Nat.pair a p))) (codedTree V) ∧
            K.value binaryCylinderBasis = treeBody V ∧
            Computes (jumpName (characteristic (KleeneNotation.iteratedJump ∅ (b a) hb)))
              (Term.closedProgram (l (Nat.pair a p))) K.val ∧
            Computes (jumpName (characteristic (KleeneNotation.iteratedJump ∅ (b a) hb)))
              (Term.closedProgram (d (Nat.pair a p))) S.val ∧
            Perfect (K.value binaryCylinderBasis) ∧ K.value binaryCylinderBasis ⊆ treeBody T ∧
            (∀ V : Set (ℕ → Bool), Perfect V → V ⊆ treeBody T → V ⊆ K.value binaryCylinderBasis) ∧
            S.value binaryCylinderBasis = treeBody T \ K.value binaryCylinderBasis := by
  obtain ⟨B,H,b,h,hB,hH,hr⟩ := uniform_notation_root_stage_deciders
  obtain ⟨F,G,f,g,hF,hG,hf,hg⟩ := uniform_tree_borel_label_indices
  obtain ⟨U,u,hU,hu⟩ := uniform_pure_tree_indices
  let l := fun z => f (h z)
  let d := fun z : ℕ => g (Nat.pair (u z.unpair.2) (h z))
  refine ⟨B,H,_,_,b,h,l,d,hB,hH,hF.comp hH,hG.comp ((hU.comp (projection_computes false)).pair hH),
    fun a ha => ?_⟩
  obtain ⟨hb,hs⟩ := hr a ha
  refine ⟨hb,fun p hp T hT hPT hstable => ?_⟩
  let W := notationOrder a ha
  let root := notationRoot a ha
  let V := stageTree W.order ((inferInstance : WellFounded W.order)) T root
  have h0 : characteristic (∅ : Set ℕ) = fun _ => 0 := by funext n; simp [characteristic]
  have hstage := hs p hp ∅ T hT (by simpa only [h0] using hPT)
  have hk := bodyLabelProgram_computes hstage
  have hd := differenceLabelProgram_computes (pureTreeProgram_decides hPT _) hstage
  obtain ⟨α,hα,hstable⟩ := hstable
  have he := notationRoot_stage_eq_stable a ha T hα hstable
  have hv : treeBody V = derivedSet (treeBody V) := by
    dsimp only [V,W,root]
    rw [he]
    exact hstable
  refine ⟨V,bodyCode V,differenceCode T V,stageTree_isSubtree W.order
    ((inferInstance : WellFounded W.order)) T hT root,hstage,value_bodyCode V,?_,?_,stable_stage_codes W.order
    ((inferInstance : WellFounded W.order)) T root hv⟩
  · simpa only [l,(hf _).2] using hk
  · simpa only [d,Nat.unpair_pair,(hg _ _).2,(hu _).2] using hd


/-- Fixing the notation fixes both label programs before any recursive tree is supplied. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    In particular, fixing a valid notation and a closed initial-tree program fixes the upper notation
    and both label programs before the recursive tree is supplied. Choose a closed named representative
    of that initial program once and evaluate the numerical maps at the fixed notation and syntax code.
-/
theorem bounded_notation_borel_codes (a : ℕ) (ha : KleeneNotation.Valid a)
    (P : AlphaTerm) (hP : P.Closed) :
    ∃ b, ∃ hb : KleeneNotation.Valid b, ∃ L D : AlphaTerm,
    ∀ T : Set (List Bool), IsSubtree T → Decides (fun _ => 0) P (codedTree T) →
      (∃ α : Ordinal, α ≤ KleeneNotation.value a ha ∧
        treeBody (ordinalStageTree T α) = derivedSet (treeBody (ordinalStageTree T α))) →
      ∃ K S : BorelExpression.Code,
        Computes (jumpName (characteristic (KleeneNotation.iteratedJump ∅ b hb))) L K.val ∧
        Computes (jumpName (characteristic (KleeneNotation.iteratedJump ∅ b hb))) D S.val ∧
        Perfect (K.value binaryCylinderBasis) ∧ K.value binaryCylinderBasis ⊆ treeBody T ∧
        (∀ V : Set (ℕ → Bool), Perfect V → V ⊆ treeBody T → V ⊆ K.value binaryCylinderBasis) ∧
        S.value binaryCylinderBasis = treeBody T \ K.value binaryCylinderBasis := by
  obtain ⟨B,H,L,D,b,h,l,d,hB,hH,hL,hD,h⟩ := uniform_bounded_notation_borel_codes
  obtain ⟨U,hU⟩ := Quotient.exists_rep P
  have hu : mk U = P := hU
  have hc : U.fv = ∅ := by rw [← hu] at hP; exact hP
  have hp : Term.closedProgram U.code = P := by
    simpa only [Term.closedProgram,Term.decode_code,hc,ite_true] using hu
  obtain ⟨hb,h⟩ := h a ha
  refine ⟨b a,hb,Term.closedProgram (l (Nat.pair a U.code)),
    Term.closedProgram (d (Nat.pair a U.code)),fun T hT hPT hs => ?_⟩
  obtain ⟨V,K,S,_,_,_,hKS⟩ := h U.code (by simpa only [Term.decode_code] using hc) T hT (by rwa [hp]) hs
  exact ⟨K,S,hKS⟩

end CantorDerivative
end PolishSpaceBook
