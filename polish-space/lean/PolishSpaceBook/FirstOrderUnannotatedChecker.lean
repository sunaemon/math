module

public import PolishSpaceBook.FirstOrderProofTreeLabels
public import PolishSpaceBook.FirstOrderLocalRuleCorrectness

@[expose] public section

/-! # A total lambda checker for unannotated membership-language proofs

The input consists only of numerical sequent labels and ordered child trees.
All primitive rule alternatives and their finite witness searches are checked
by the closed lambda term, including on arbitrary malformed numerical inputs.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
open NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
set_option backward.isDefEq.respectTransparency.types false

theorem checked_iff_valid {D : Data} {T : SequentTree membershipLanguage}
    (h : Represents D T) : Checked D ↔ T.Valid := by
  cases h with
  | @node n s ds ts hn hds =>
    have hc : ∀ d ∈ ds, ∀ t, Represents d t → (Checked d ↔ t.Valid) := by
      intro d hd t hdt
      exact checked_iff_valid hdt
    have hchildren : (∀ d ∈ ds, Checked d) ↔ (∀ t ∈ ts, t.Valid) := by
      clear hn
      induction hds with
      | nil => simp
      | @cons d t ds ts hdt hrest ih =>
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_congr (hc d (by simp) t hdt) (ih (fun d hd => hc d (by simp [hd])))
    have hr := LocalRulePrograms.checker_parsed_iff n (ds.map Data.root) s
      (ts.map SequentTree.root) hn (represents_roots hds)
    constructor
    · intro hcheck
      cases hcheck with
      | node _ hlocal hchildren' => exact .node (hr.mp hlocal) (hchildren.mp hchildren')
    · intro hvalid
      cases hvalid with
      | node hlocal hchildren' =>
        exact .node ((LocalRulePrograms.validSequent_ne_zero Grammar.Program.ident n).mpr ⟨s, hn⟩)
          (hr.mpr hlocal) (hchildren.mpr hchildren')
termination_by sizeOf D
decreasing_by
  have hh := List.sizeOf_lt_of_mem hd
  simp only [Data.node.sizeOf_spec]
  omega

/-- Every natural number is classified by parsing its actual syntax and
checking precisely the primitive rules of the book. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Deduction.** The formal derivability relation is the syntactic side of the later comparison with classical semantic
    truth. A \termdefine{sequent} in a language $L$ is a pair $\Gamma \vdash \varphi$ in which the
    \termdefineas{hypothesis}{hypotheses} $\Gamma$ form a finite set of $L$-formulas and the \termdefine{conclusion}
    $\varphi$ is an $L$-formula. We write $\Gamma,\varphi$ for $\Gamma \cup \{\varphi\}$. Thus an assumption may be used
    repeatedly inside a proof; this is contraction, built into the finite-set convention. Each \termdefine{inference rule}
    below — one or two rules per connective, plus an axiom (Ax) for assumption, equality rules ($=$I, $=$E), and classically
    the law of excluded middle (LEM) — is a syntactic relation between a finite list of premise sequents and a conclusion
    sequent: given a candidate $(S_1, \ldots, S_n; S)$, one checks whether the tuple matches the rule schema and satisfies
    its side condition. \termdefineas{introduction rule}{Introduction} rules (I) build a connective into the conclusion;
    \termdefineas{elimination rule}{elimination} rules (E) decompose a connective in a hypothesis or premise. A
    \termdefine{proof} is a finite rooted tree whose nodes are labeled by sequents such that, at each non-leaf node $S$, the
    labels of its children are the premises of some rule instance with conclusion $S$, and each leaf is the conclusion of a
    nullary rule.
-/
theorem accepts_iff_valid_tree (n : ℕ) :
    accepts n ↔ ∃ D T, parseCode n = some D ∧ Represents D T ∧ T.Valid := by
  rw [accepts_iff_parsed_checked]
  constructor
  · rintro ⟨D, hp, hc⟩
    obtain ⟨T, hT⟩ := hc.exists_interpretation
    exact ⟨D, T, hp, hT, (checked_iff_valid hT).mp hc⟩
  · rintro ⟨D, T, hp, hT, hv⟩
    exact ⟨D, hp, (checked_iff_valid hT).mpr hv⟩

theorem checker_accepts_valid {n : ℕ} {D : Data} {T : SequentTree membershipLanguage}
    (hp : parseCode n = some D) (hT : Represents D T) (hv : T.Valid) :
    Relation.ReflTransGen AlphaTerm.Beta
      (AlphaTerm.app checker.term (AlphaTerm.numeral n)) (AlphaTerm.numeral 1) := by
  have ha := (accepts_iff_valid_tree n).mpr ⟨D, T, hp, hT, hv⟩
  simpa only [ha, ↓reduceIte] using checker_apply n

theorem checker_rejects_invalid (n : ℕ)
    (h : ¬∃ D T, parseCode n = some D ∧ Represents D T ∧ T.Valid) :
    Relation.ReflTransGen AlphaTerm.Beta
      (AlphaTerm.app checker.term (AlphaTerm.numeral n)) (AlphaTerm.numeral 0) := by
  have ha : ¬accepts n := fun ha => h ((accepts_iff_valid_tree n).mp ha)
  simpa only [ha, ↓reduceIte] using checker_apply n

/-- Existence of an accepted finite input is exactly actual derivability;
there is no decision of derivability or supplied inference annotation. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Since hypotheses are
    finite sets, exchange and contraction are built in. A sequent $\Gamma \vdash\varphi$ is
    \termdefine{derivable} iff some proof has it as root. The renaming and weakening lemma below justifies enlarging
    the hypothesis set, including the necessary changes of eigenvariables.
-/
theorem derives_iff_accepted_code (Γ : Context membershipLanguage)
    (φ : AlphaFormula membershipLanguage) :
    Derives Γ φ ↔ ∃ n D, parseCode n = some D ∧
      LocalRulePrograms.parseSequent D.root = some (Γ, φ) ∧ accepts n := by
  constructor
  · intro h
    obtain ⟨T, hroot, hv⟩ := h.exists_valid_tree
    obtain ⟨D, hD⟩ := exists_representative T
    exact ⟨D.encode.code, D, parseCode_encode D, by simpa only [hroot] using hD.root,
      (accepts_encode_iff D).mpr ((checked_iff_valid hD).mpr hv)⟩
  · rintro ⟨n, D, hp, hroot, ha⟩
    obtain ⟨E, T, hE, hT, hv⟩ := (accepts_iff_valid_tree n).mp ha
    have heq : E = D := Option.some.inj (hE.symm.trans hp)
    subst E
    have hs : T.root = (Γ, φ) := Option.some.inj (hT.root.symm.trans hroot)
    simpa only [hs] using hv.derives

end PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
