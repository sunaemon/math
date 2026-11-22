module

public import PolishSpaceBook.FirstOrderEffectiveTreeLabels
public import PolishSpaceBook.FirstOrderEffectiveRuleCorrectness
public import PolishSpaceBook.FirstOrderNumericalProofTrees

@[expose] public section

/-! # Total unannotated proof checking for every effective signature

The structural fold is instantiated with the actual signature-dependent sequent
grammar and seventeen-rule program. Neither local-rule correctness nor witness
synthesis is an input assumption of the resulting derivability equivalence.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.ProofChecker
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.ProofTreeProgram (Data parseCode_encode)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option backward.isDefEq.respectTransparency.types false

def config : NumericalProofTrees.Config :=
  ⟨EffectiveRulePrograms.validSequent S Grammar.Program.ident, EffectiveRulePrograms.checker S⟩

def program : Grammar.Program := NumericalProofTrees.checker (config S)
def accepts (n : ℕ) : Prop := NumericalProofTrees.accepts (config S) n
instance proofCodeAcceptanceDecidable (n : ℕ) : Decidable (accepts S n) :=
  inferInstanceAs (Decidable (NumericalProofTrees.accepts (config S) n))

theorem checked_has_rep {D : Data} (h : NumericalProofTrees.Checked (config S) D) :
    ∃ T, S.TreeRep D T := by
  induction h with
  | @node n ds hn hr hc ih =>
    obtain ⟨s, hs⟩ := (EffectiveRulePrograms.validSequent_correct S Grammar.Program.ident n).mp hn
    have hl : ∃ ts, List.Forall₂ (TreeRep S) ds ts := by
      clear hr hc
      induction ds with
      | nil => exact ⟨[], .nil⟩
      | cons d ds ihds =>
        obtain ⟨t, ht⟩ := ih d (by simp)
        obtain ⟨ts, hts⟩ := ihds (fun d hd => ih d (by simp [hd]))
        exact ⟨t :: ts, .cons ht hts⟩
    obtain ⟨ts, hts⟩ := hl
    exact ⟨.node s ts, .node hs hts⟩

theorem checked_iff_valid {D : Data} {T : SequentTree L} (h : S.TreeRep D T) :
    NumericalProofTrees.Checked (config S) D ↔ T.Valid := by
  cases h with
  | @node n s ds ts hn hds =>
    have hc : ∀ d ∈ ds, ∀ t, S.TreeRep d t →
        (NumericalProofTrees.Checked (config S) d ↔ t.Valid) := by
      intro d hd t hdt
      exact checked_iff_valid hdt
    have hchildren : (∀ d ∈ ds, NumericalProofTrees.Checked (config S) d) ↔
        (∀ t ∈ ts, t.Valid) := by
      clear hn
      induction hds with
      | nil => simp
      | @cons d t ds ts hdt hrest ih =>
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_congr (hc d (by simp) t hdt) (ih (fun d hd => hc d (by simp [hd])))
    have hr := EffectiveRulePrograms.checker_rep_iff S n (ds.map Data.root) s
      (ts.map SequentTree.root) hn (treeRep_roots S hds)
    constructor
    · intro hcheck
      cases hcheck with
      | node _ hlocal hchildren' => exact .node (hr.mp hlocal) (hchildren.mp hchildren')
    · intro hvalid
      cases hvalid with
      | node hlocal hchildren' =>
        exact .node ((EffectiveRulePrograms.validSequent_correct S Grammar.Program.ident n).mpr ⟨s, hn⟩)
          (hr.mpr hlocal) (hchildren.mpr hchildren')
termination_by sizeOf D
decreasing_by
  have hh := List.sizeOf_lt_of_mem hd
  simp only [Data.node.sizeOf_spec]
  omega

def ValidCode (n : ℕ) : Prop := ∃ D T, ProofTreeProgram.parseCode n = some D ∧ S.TreeRep D T ∧ T.Valid

theorem accepts_iff_validCode (n : ℕ) : accepts S n ↔ ValidCode S n := by
  rw [accepts, NumericalProofTrees.accepts_iff_parsed_checked]
  constructor
  · rintro ⟨D, hp, hc⟩
    obtain ⟨T, hT⟩ := checked_has_rep S hc
    exact ⟨D, T, hp, hT, (checked_iff_valid S hT).mp hc⟩
  · rintro ⟨D, T, hp, hT, hv⟩
    exact ⟨D, hp, (checked_iff_valid S hT).mpr hv⟩

/-- This decision is supplied by the proved numerical lambda computation. -/
instance validCodeDecidable (n : ℕ) : Decidable (ValidCode S n) :=
  decidable_of_iff (accepts S n) (accepts_iff_validCode S n)

theorem program_closed : (program S).term.Closed := NumericalProofTrees.checker_closed (config S)

/-- All raw numerical inputs terminate, and precisely valid proof codes return one. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: statement
  kind: proposition
  title: Effective proof-tree checking
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Finally apply a structural lambda fold to the proposed tree, carrying the root labels of its children and their
    acceptance bits. Reject malformed labels, malformed tree structure, or any failed local test. Each numerical
    subroutine is total, and the fold descends through proper syntax subtrees, so it halts on every numerical input.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For effectively presented languages such as $L_\in$, the set of proofs is decidable.
-/
theorem program_decides (n : ℕ) : Relation.ReflTransGen AlphaTerm.Beta
    (AlphaTerm.app (program S).term (AlphaTerm.numeral n))
    (AlphaTerm.numeral (if ValidCode S n then 1 else 0)) := by
  have hh := NumericalProofTrees.checker_apply (config S) n
  simpa only [program, ← accepts_iff_validCode S n, accepts] using hh

theorem program_rejects_invalid (n : ℕ) (h : ¬ValidCode S n) : Relation.ReflTransGen AlphaTerm.Beta
    (AlphaTerm.app (program S).term (AlphaTerm.numeral n)) (AlphaTerm.numeral 0) := by
  simpa only [h, ↓reduceIte] using program_decides S n

/-- Acceptance can be expressed directly as reduction of the constructed term. -/
theorem program_beta_one_iff (n : ℕ) :
    Relation.ReflTransGen AlphaTerm.Beta
      (AlphaTerm.app (program S).term (AlphaTerm.numeral n)) (AlphaTerm.numeral 1) ↔ ValidCode S n := by
  constructor
  · intro h
    have he := AlphaTerm.numeral_output_unique h (program_decides S n)
    by_contra hn
    simp only [hn, ↓reduceIte] at he
    omega
  · intro h
    simpa only [h, ↓reduceIte] using program_decides S n

theorem derives_iff_accepted_code (Γ : Context L) (φ : AlphaFormula L) :
    Derives Γ φ ↔ ∃ n D, ProofTreeProgram.parseCode n = some D ∧ S.SequentRep D.root (Γ, φ) ∧ accepts S n := by
  constructor
  · intro h
    obtain ⟨T, hroot, hv⟩ := h.exists_valid_tree
    obtain ⟨D, hD⟩ := S.tree_has_code T
    exact ⟨D.encode.code, D, parseCode_encode D, by simpa only [hroot] using TreeRep.root S hD,
      (NumericalProofTrees.accepts_encode_iff (config S) D).mpr ((checked_iff_valid S hD).mpr hv)⟩
  · rintro ⟨n, D, hp, hroot, ha⟩
    obtain ⟨E, T, hE, hT, hv⟩ := (accepts_iff_validCode S n).mp ha
    have heq : E = D := Option.some.inj (hE.symm.trans hp)
    subst E
    have hs : T.root = (Γ, φ) := S.sequentRep_unique (TreeRep.root S hT) hroot
    simpa only [hs] using hv.derives

/-- The derivability endpoint uses literal beta acceptance by the closed term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Induction on an accepted tree turns its verified local rules into a derivation. Conversely, induction on a
    derivation produces a finite sequent-labelled tree; choose representatives of its finitely many formula classes
    and contexts and encode them. The local equivalences show that every node is accepted. This proves the stated
    equivalence with existence of an accepted code, while deciding only each supplied finite tree.
-/
theorem derives_iff_beta_code (Γ : Context L) (φ : AlphaFormula L) :
    Derives Γ φ ↔ ∃ n D, ProofTreeProgram.parseCode n = some D ∧
      S.SequentRep D.root (Γ, φ) ∧ Relation.ReflTransGen AlphaTerm.Beta
        (AlphaTerm.app (program S).term (AlphaTerm.numeral n)) (AlphaTerm.numeral 1) := by
  simp only [program_beta_one_iff, ← accepts_iff_validCode]
  exact derives_iff_accepted_code S Γ φ

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.ProofChecker
