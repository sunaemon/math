module

public import PolishSpaceBook.LambdaBairePreimages
public import PolishSpaceBook.LambdaLusinSuslinPrefixes
public import PolishSpaceBook.LambdaTemplateIndices

@[expose] public section

/-! # Closed-graph indices from a map and a closed domain

Every finite test terminates on every index. Graph correctness needs the map
program to terminate only on its stated domain. The tree carries exactly the
output and its preimage, without an additional certificate branch coordinate.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance lusinGraphListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance lusinGraphPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The program index remains a numerical input to the finite graph-row tester. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform closed-graph row tests
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    List pairing and list access supply the two padded coordinate words. Input substitution supplies
    the paired parameter and input digits to the universal finite-candidate tester, while the numerical
    projections supply the program index and proposed output data. The equality test and Boolean
    implication then give the row bit. In the bounded-prefix loop, retain the family index alongside
    the word pair when forming each row query; truncate both words to the row's prescribed bound.
    A relative bounded product combines the finitely many bits. Finally apply the finite-check-tree
    construction. Each query uses the original parameter, and every finite node requires only finitely
    many terminating tests. Specializing this joint decider gives the graph-index generator.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The graph-row tester of §{sec:lambda-graph-tests} can receive the program index as numerical data.
    For input $z=\NatPair{e}{\NatPair{i}{\NatPair{u}{v}}}$, regard $u$ as the output-word code and
    $v$ as the input-word code. The universal tester needs the input digit first in each digit pair, so the
    digit-pairing term receives $v,u$.
    Extract all fields by projections, write
    $i=\NatPair{n}{\NatPair{m}{r}}$, and put
    $$\begin{aligned}
    \LambdaTermName{pairedDigits}(z)&:=\LambdaListPair(\LambdaNumericPair\,v\,u),\\
    \LambdaTermName{queryDigit}(o,z,k)&:=\LambdaNumericPair\,(ok)\,
      \bigl(\LambdaNumericProjection{1}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,k))\bigr),\\
    \LambdaTermName{rowCandidate}(o,z)&:= \LambdaQueryOutputCandidate\,( \lambdaab{k}{
    \LambdaTermName{queryDigit}(o,z,k)})\,e\,n\,
      (\LambdaNumericPair\,m\,r),\\
    \LambdaTermName{rowEqual}(z)&:=\LambdaEqual\,
      \bigl(\LambdaNumericProjection{2}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,n))\bigr)\,m.
    \end{aligned}$$
    The row requires the implication from the candidate bit to the equality bit. Bit implication is
    computed by the Boolean constructions of §{sec:lambda-comparison-programs}. Expand the fields
    and use fresh binders. Every operation terminates on every finite input: the candidate test checks
    bounded evidence rather than running the indexed program until it stops.
-/
theorem graphClause_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × PrefixPair) =>
      graphClause ε z.1 z.2.1 z.2.2.1) := by
  have hU : UniformNumericalComputes uniformCandidateProgram (fun p z =>
      if Term.oracleOutputCandidate p z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 then 1 else 0) :=
    ⟨uniformCandidateProgram_closed,fun p z => (uniformCandidateProgram_computes p).2 z⟩
  have hindex := (projection_computes true).pair
    ((projection_computes true).comp (projection_computes false))
  have ha := graphInputAccess_computes.reindex
    (((projection_computes false).comp (projection_computes true)).pair (projection_computes false))
  have hc := (hU.reindex hindex).dataInput ha
  have hc' : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      Term.oracleOutputCandidate (fun j => Nat.pair (ε j)
        (((NatListCode.decode z.unpair.2.unpair.2.unpair.1).getD j 0).unpair.1))
        z.unpair.1 z.unpair.2.unpair.1.unpair.1 z.unpair.2.unpair.1.unpair.2 = true) := by
    refine ⟨_,hc.1,fun z => ⟨?_,?_⟩⟩ <;> intro hz
    · simpa only [Encodable.encode_nat,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,hz] using hc.2 ε z
    · simpa only [Encodable.encode_nat,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,hz] using hc.2 ε z
  have he' : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      ((NatListCode.decode z.unpair.2.unpair.2.unpair.1).getD z.unpair.2.unpair.1.unpair.1 0).unpair.2 =
        z.unpair.2.unpair.1.unpair.2.unpair.1) := by
    apply numericalDecision (graphEquality_computes.comp (projection_computes false)) ε
    · intro z hz; exact ite_eq_left hz
    · intro z hz; exact ite_eq_right hz
  simpa [graphClause,Encodable.encode,Encodable.encodeSigma] using (hc'.imp he').precompNumerical
    (g := fun z : ℕ × (ℕ × PrefixPair) => Encodable.encode z) numericalIdentity_computes (fun _ => rfl)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    First compute the index $\delta(p)$ of the closed pair-node program
    $$\lambdaab{o}{\lambdaab{z}{P_p o(\LambdaNumericProjection{2}z)}}.$$
    The corresponding indexed tree has body $\BaireSpace\times F$: a branch survives exactly when
    all prefixes of its second coordinate pass the domain test. Syntax substitution computes this
    index without executing the domain program. For the graph condition, use rows
    $i=\NatPair{n}{\NatPair{m}{r}}$. On a prefix pair of length $i+1$, test whether a computation
    certificate within bound $r$ returns $m$ at coordinate $n$; if so, require that the output prefix
    has that digit. The stage-address bound of §{sec:lambda-stage-address-bound} makes the finite
    input prefix sufficient. §{sec:lambda-closed-graph-indices} gives a single row tester
    with the map index supplied as numerical data. Conjoin the domain-tree test with all graph rows
    whose prescribed prefixes fit, and apply the finite-check-tree construction. This gives a jointly
    decidable family, so numerical specialization gives $\gamma(e,p)$.
-/
/-- Convert a prefix-domain program to a pair-node program reading the second word. -/
theorem uniform_domain_pair_indices :
    ∃ D d, NumericalComputes D d ∧ ∀ p,
      Term.closedProgram (d p) = reindexProgram (Term.closedProgram p) (numericalProjectionTerm false) := by
  have hN : NumericalComputes programCodeTerm (fun e => (Term.programSyntax e).code) :=
    ⟨programCodeTerm_closed,programCodeTerm_apply⟩
  obtain ⟨D,d,hD,hd⟩ := uniform_template_indices (reindexProgram (var 86) (numericalProjectionTerm false)) 86
  refine ⟨_,_,hD.comp hN,fun p => ?_⟩
  have h := hd (Term.programSyntax p).code
  simp only [Term.decode_code,Term.mk_programSyntax] at h
  have hv (i : ℕ) : i ∉ (Term.closedProgram p).fv := by rw [Term.closedProgram_closed]; simp
  simp only [reindexProgram,subst_lam_fresh _ _ 1 86 (by decide) (hv 1),
    subst_lam_fresh _ _ 2 86 (by decide) (hv 2),subst_app,subst_var,ite_true,ite_false,
    show (1 : ℕ) ≠ 86 from by decide,show (2 : ℕ) ≠ 86 from by decide,
    subst_closed _ _ _ (projection_computes false).1] at h
  have hc : (Term.decode (d (Term.programSyntax p).code)).fv = ∅ := by
    change (mk (Term.decode (d (Term.programSyntax p).code))).Closed
    rw [h]
    exact reindexProgram_closed (Term.closedProgram_closed p) (projection_computes false).1
  exact (ite_eq_left hc).trans h

def graphWitnessClause (ε : ℕ → ℕ) (e i : ℕ) (z : PrefixPair) : Prop :=
  graphClause ε e i (pairWords z.2 z.1)

theorem graphWitnessClause_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × PrefixPair) =>
      graphWitnessClause ε z.1 z.2.1 z.2.2) := by
  have he := projection_computes true
  have hi := (projection_computes true).comp (projection_computes false)
  have hw := (projection_computes false).comp (projection_computes false)
  have hp := pairWords_computes.comp
    (((projection_computes false).comp hw).pair ((projection_computes true).comp hw))
  have h := (graphClause_family_decidable ε).precompNumerical
    (g := fun z : ℕ × (ℕ × PrefixPair) => (z.1,(z.2.1,(pairWords z.2.2.2 z.2.2.1,[]))))
    (he.pair (hi.pair (hp.pair (numericalConstant_computes 0))))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma,NatListCode.encode])
  exact h

def closedGraphTest (ε : ℕ → ℕ) (i : ℕ) (z : PrefixPair) : Prop :=
  z ∈ (indexedTree ε i.unpair.2).tree ∧
    boundedPrefixTest (graphWitnessClause ε i.unpair.1) Nat.succ z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform closed-graph row tests
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The graph-row tester of §{sec:lambda-graph-tests} can receive the program index as numerical data.
    For input $z=\NatPair{e}{\NatPair{i}{\NatPair{u}{v}}}$, regard $u$ as the output-word code and
    $v$ as the input-word code. The universal tester needs the input digit first in each digit pair, so the
    digit-pairing term receives $v,u$.
    Extract all fields by projections, write
    $i=\NatPair{n}{\NatPair{m}{r}}$, and put
    $$\begin{aligned}
    \LambdaTermName{pairedDigits}(z)&:=\LambdaListPair(\LambdaNumericPair\,v\,u),\\
    \LambdaTermName{queryDigit}(o,z,k)&:=\LambdaNumericPair\,(ok)\,
      \bigl(\LambdaNumericProjection{1}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,k))\bigr),\\
    \LambdaTermName{rowCandidate}(o,z)&:= \LambdaQueryOutputCandidate\,( \lambdaab{k}{
    \LambdaTermName{queryDigit}(o,z,k)})\,e\,n\,
      (\LambdaNumericPair\,m\,r),\\
    \LambdaTermName{rowEqual}(z)&:=\LambdaEqual\,
      \bigl(\LambdaNumericProjection{2}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,n))\bigr)\,m.
    \end{aligned}$$
    The row requires the implication from the candidate bit to the equality bit. Bit implication is
    computed by the Boolean constructions of §{sec:lambda-comparison-programs}. Expand the fields
    and use fresh binders. Every operation terminates on every finite input: the candidate test checks
    bounded evidence rather than running the indexed program until it stops.
-/
theorem closedGraphTest_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair => closedGraphTest ε z.1 z.2) := by
  have hd := indexedTree_reindex_decidable ε (projection_computes false)
  have hg := (boundedPrefixTest_family_decidable (graphWitnessClause_family_decidable ε)
    successor_computes).precompNumerical
    (g := fun z : ℕ × PrefixPair => (z.1.unpair.1,z.2))
    (((projection_computes true).comp (projection_computes true)).pair (projection_computes false))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa only [closedGraphTest,ite_true,Bool.false_eq_true,ite_false] using hd.and hg

def closedGraphTree (ε : ℕ → ℕ) (i : ℕ) : PairTree ε :=
  finiteCheckTree (closedGraphTest ε i)
    ((closedGraphTest_family_decidable ε).precompNumerical
      (g := fun z : PrefixPair => (i,z))
      ((numericalConstant_computes i).pair numericalIdentity_computes)
      (fun z => by simp [Encodable.encode,Encodable.encodeSigma]))

theorem closedGraphTree_family_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair =>
      z.2 ∈ (closedGraphTree ε z.1).tree) :=
  finiteCheck_family_decidable (closedGraphTest_family_decidable ε)

theorem pairTreeBody_closedGraphTree (ε : ℕ → ℕ) (e d : ℕ) (y x : ℕ → ℕ) :
    (y,x) ∈ pairTreeBody (closedGraphTree ε (Nat.pair e d)).tree ↔
      (y,x) ∈ pairTreeBody (indexedTree ε d).tree ∧
      ∀ i, graphClause ε e i (seqPrefix (pairBaire x y) (i+1)) := by
  change (y,x) ∈ pairTreeBody (finiteCheckNodes _) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  simp only [closedGraphTest,Nat.unpair_pair,mem_ofPred_eq,forall_and,
    boundedPrefixTest_iff,graphWitnessClause,pairWords_prefix,Nat.succ_eq_add_one,pairTreeBody]

/-- The supplied map need terminate only on the body of the supplied domain tree. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Uniform closed-graph indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For correctness, the domain tests force $x\in F$. At such a point every output coordinate has a
    finite computation certificate. Thus the graph rows force $y(n)=f(x)(n)$ for every $n$.
    Conversely, on the actual graph every certified output has the correct value by uniqueness of
    numerical outputs, so all tests hold. The tree has exactly the output and preimage coordinates.
    If the map is injective, each output section therefore contains at most one branch.
-/
theorem uniform_closed_graph_indices (ε : ℕ → ℕ) :
    ∃ G g, NumericalComputes G g ∧ ∀ e p (T : Set (List ℕ)),
      LambdaRelative.Decides ε (Term.closedProgram p) (· ∈ T) →
      ∀ F : treeBody T → (ℕ → ℕ),
        (∀ x n, OracleRuns (pairBaire ε x.val) (Term.closedProgram e) n (F x n)) →
        ∀ y x, (y,x) ∈ pairTreeBody (indexedTree ε (g (Nat.pair e p))).tree ↔
          ∃ hx : x ∈ treeBody T, y = F ⟨x,hx⟩ := by
  obtain ⟨D,d,hD,hd⟩ := uniform_domain_pair_indices
  obtain ⟨g,⟨G,hG⟩,hg⟩ := treeFamily_indices ε (closedGraphTree ε) (closedGraphTree_family_decidable ε)
  have h := hG.comp ((projection_computes true).pair (hD.comp (projection_computes false)))
  refine ⟨_,_,h,fun e p T hT F hF y x => ?_⟩
  simp only [Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false]
  rw [pairTreeBody_indexedTree ε _ _ (hg _),pairTreeBody_closedGraphTree]
  have hdT : TreeIndex ε (d p) {z : PrefixPair | z.2 ∈ T} := by
    rw [TreeIndex,hd p]
    exact hT.precompNumerical (g := fun z : PrefixPair => z.2) (projection_computes false)
      (fun z => by simp [Encodable.encode])
  rw [pairTreeBody_indexedTree ε _ _ hdT]
  change (x ∈ treeBody T ∧ ∀ i, graphClause ε e i (seqPrefix (pairBaire x y) (i+1))) ↔ _
  constructor
  · rintro ⟨hx,hg⟩
    exact ⟨hx,(forall_graphClause_iff_at (hF ⟨x,hx⟩) y).mp hg⟩
  · rintro ⟨hx,hy⟩
    exact ⟨hx,(forall_graphClause_iff_at (hF ⟨x,hx⟩) y).mpr hy⟩

/-- Compose graph compilation with the separated-prefix compilers, keeping all input indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Preimage prefix indices from map and domain indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The graph compiler preserves the graph itself, so injectivity gives the unique-section hypothesis
    of the prefix-test proposition. Compose its two total numerical maps with the graph-index map.
    The graph identity identifies the projection with the range and gives the asserted prefix equivalence.
-/
theorem uniform_map_prefix_indices (ε : ℕ → ℕ) :
    ∃ (G C D : AlphaTerm) (g c d : ℕ → ℕ),
      NumericalComputes G g ∧ NumericalComputes C c ∧ NumericalComputes D d ∧
      ∀ e p (T : Set (List ℕ)), LambdaRelative.Decides ε (Term.closedProgram p) (· ∈ T) →
      ∀ F : treeBody T → (ℕ → ℕ),
        (∀ x n, OracleRuns (pairBaire ε x.val) (Term.closedProgram e) n (F x n)) →
        Function.Injective F →
        pairTreeProjection (indexedTree ε (g (Nat.pair e p))).tree = Set.range F ∧
        ∀ s, indexedProjection ε (c (Nat.pair (Nat.pair e p) s)) =
          (indexedProjection ε (d (Nat.pair (Nat.pair e p) s)))ᶜ ∧
          ∀ x, F x ∈ indexedProjection ε (c (Nat.pair (Nat.pair e p) s)) ↔
            x.val ∈ cyl (NatListCode.decode s) := by
  obtain ⟨G,g,hG,hg⟩ := uniform_closed_graph_indices ε
  obtain ⟨C,D,c,d,hC,hD,hprefix⟩ := uniform_separated_prefix_indices ε
  have hc := hC.comp ((hG.comp (projection_computes true)).pair (projection_computes false))
  have hd := hD.comp ((hG.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨G,_,_,g,_,_,hG,hc,hd,fun e p T hT F hF hinj => ?_⟩
  have hgraph := hg e p T hT F hF
  have hu : UniqueSections (indexedTree ε (g (Nat.pair e p))).tree := by
    intro y x x' hx hx'
    obtain ⟨hx,hfx⟩ := (hgraph y x).mp hx
    obtain ⟨hx',hfx'⟩ := (hgraph y x').mp hx'
    exact congrArg Subtype.val (hinj (hfx.symm.trans hfx'))
  constructor
  · ext y
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx,hy⟩ := (hgraph y x).mp hx
      exact ⟨⟨x,hx⟩,hy.symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,(hgraph (F x) x.val).mpr ⟨x.property,rfl⟩⟩
  · intro s
    simp only [Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false]
    obtain ⟨hcompl,hpre⟩ := hprefix (g (Nat.pair e p)) hu s
    exact ⟨hcompl,fun x => hpre (F x) x.val ((hgraph (F x) x.val).mpr ⟨x.property,rfl⟩)⟩

end LambdaTree
end PolishSpaceBook
