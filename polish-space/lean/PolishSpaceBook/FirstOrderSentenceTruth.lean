module

public import PolishSpaceBook.FirstOrderMaximalQuantifiers

@[expose] public section

/-!
# The term-model truth lemma for sentences

Strong induction counts formula constructors, not the size of terms. A closed
instance of a quantified body has the body's constructor count, so the
induction hypothesis applies to every closed instance without assuming the
assignment form of the truth lemma.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

/-- A named term with no variables is the image of a canonical closed term. -/
theorem exists_closedTerm (t : L.Term ℕ) (ht : t.varFinset = ∅) :
    ∃ r : L.Term Empty, namedClosedTerm r = t := by
  induction t with
  | var x => simp [Term.varFinset] at ht
  | func f ts ih =>
    have hts (i) : (ts i).varFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm : x ∈ (Term.func f ts).varFinset := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
      simp only [ht, Finset.notMem_empty] at hm
    choose rs hrs using (fun i => ih i (hts i))
    refine ⟨.func f rs, ?_⟩
    simp only [namedClosedTerm_func]
    exact congrArg (Term.func f) (funext hrs)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now prove the truth lemma for sentences by strong induction on the number of formula constructors, without counting
    constructors inside terms. The atomic cases are the \termuse{term-model construction lemma}; the Boolean cases
    follow from the membership rules above. For a quantified sentence, substitute a closed term for the quantified
    variable in its body. The result is a sentence, and substitution leaves its number of formula constructors unchanged,
    so it is smaller than the original quantified formula. Apply the induction hypothesis to every such instance.
    The substitution lemma and evaluation of closed terms identify the truth of the instance with truth of the body
    under the assignment of that term's class to the quantified variable. Every element of the model is represented
    by a closed term, so the displayed membership rules give exactly the semantic quantifier clauses.
-/
theorem Formula.termModel_truth_sentence {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) (φ : Formula L) (hclosed : φ.fv = ∅) (s : ℕ → TermModel T) :
    φ.Realize s ↔ AlphaFormula.mk φ ∈ T := by
  suffices h : ∀ N (ψ : Formula L), ψ.nodes ≤ N → ψ.fv = ∅ → ∀ a : ℕ → TermModel T,
      ψ.Realize a ↔ AlphaFormula.mk ψ ∈ T from h φ.nodes φ le_rfl hclosed s
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ψ hsize hfv a
    cases ψ with
    | falsum => exact ⟨False.elim, hT.falsum_not_mem⟩
    | equal t r =>
      have ht : t.varFinset = ∅ := (Finset.union_eq_empty.mp hfv).1
      have hr : r.varFinset = ∅ := (Finset.union_eq_empty.mp hfv).2
      obtain ⟨t', rfl⟩ := exists_closedTerm t ht
      obtain ⟨r', rfl⟩ := exists_closedTerm r hr
      exact (realize_closedEq T t' r' a).trans (hT.mem_iff_proves (by simp [Sentences])).symm
    | rel R ts =>
      have hts (i) : (ts i).varFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hm : x ∈ (Formula.rel R ts).fv := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
        simp [hfv] at hm
      choose rs hrs using (fun i => exists_closedTerm (ts i) (hts i))
      have he : (fun i => namedClosedTerm (rs i)) = ts := funext hrs
      rw [← he]
      exact (realize_closedRel T R rs a).trans (hT.mem_iff_proves (by simp [Sentences])).symm
    | binary c ψ χ =>
      have hp : ψ.fv = ∅ := (Finset.union_eq_empty.mp hfv).1
      have hq : χ.fv = ∅ := (Finset.union_eq_empty.mp hfv).2
      have hsp : ψ.nodes < N := by change ψ.nodes + χ.nodes + 1 ≤ N at hsize; omega
      have hsq : χ.nodes < N := by change ψ.nodes + χ.nodes + 1 ≤ N at hsize; omega
      change c.eval (ψ.Realize a) (χ.Realize a) ↔ AlphaFormula.binary c (AlphaFormula.mk ψ) (AlphaFormula.mk χ) ∈ T
      exact (c.eval_congr (ih _ hsp ψ le_rfl hp a) (ih _ hsq χ le_rfl hq a)).trans
        (hT.binary_mem_iff c hp hq).symm
    | quant q x ψ =>
      have hp : (mk ψ).fv ⊆ {x} := oneVariable_of_quant_sentence q hfv
      have hi (t : L.Term Empty) :
          ψ.Realize (Function.update a x (termClass T t)) ↔ (mk ψ).subst x (namedClosedTerm t) ∈ T := by
        have hs : (ψ.subst x (namedClosedTerm t)).nodes < N := by
          rw [Formula.nodes_subst]
          change ψ.nodes + 1 ≤ N at hsize
          omega
        have hc : (ψ.subst x (namedClosedTerm t)).fv = ∅ := oneVariable_subst_sentence hp t
        have hinst := ih _ hs (ψ.subst x (namedClosedTerm t)) le_rfl hc a
        have hsem := Formula.realize_subst ψ x (namedClosedTerm t) a
        rw [realize_namedClosedTerm] at hsem
        exact hsem.symm.trans hinst
      cases q with
      | ex =>
        change (∃ b : TermModel T, ψ.Realize (Function.update a x b)) ↔ AlphaFormula.quant .ex x (AlphaFormula.mk ψ) ∈ T
        rw [hT.ex_mem_iff hH hp]
        constructor
        · rintro ⟨b, hb⟩
          obtain ⟨t, rfl⟩ := Quotient.exists_rep b
          exact ⟨t, (hi t).mp hb⟩
        · rintro ⟨t, ht⟩
          exact ⟨termClass T t, (hi t).mpr ht⟩
      | all =>
        change (∀ b : TermModel T, ψ.Realize (Function.update a x b)) ↔ AlphaFormula.quant .all x (AlphaFormula.mk ψ) ∈ T
        rw [hT.all_mem_iff hH hp]
        constructor
        · intro ha t
          exact (hi t).mp (ha (termClass T t))
        · intro ht b
          obtain ⟨t, rfl⟩ := Quotient.exists_rep b
          exact (hi t).mpr (ht t)

/-- The sentence truth lemma on the alpha-classes used by the proof system. -/
theorem AlphaFormula.termModel_truth_sentence {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) (φ : AlphaFormula L) (hclosed : φ ∈ Sentences L) (s : ℕ → TermModel T) :
    φ.Realize s ↔ φ ∈ T := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.termModel_truth_sentence hT hH φ hclosed s

end PolishSpaceBook.NamedFirstOrder
