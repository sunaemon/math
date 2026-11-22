module

public import PolishSpaceBook.FirstOrderProofTreeCorrectness
public import PolishSpaceBook.FirstOrderLocalSequentInterpretation

@[expose] public section

/-! # Mathematical interpretation of the numerical tree labels

Every finite context and alpha-class has a numerical representative. The choice
below is used only to prove existence of a finite input; the checker itself
operates on the numerical labels and makes no such choice.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
open NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
set_option backward.isDefEq.respectTransparency.types false

theorem exists_sequent_code (s : Sequent membershipLanguage) :
    ∃ n, LocalRulePrograms.parseSequent n = some s := by
  classical
  obtain ⟨Γ, φ⟩ := s
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep φ
  have contexts : ∀ Γ : Context membershipLanguage,
      ∃ xs : List FOL, ContextPrograms.context xs = Γ := by
    intro Γ
    induction Γ using Finset.induction_on with
    | empty => exact ⟨[], rfl⟩
    | @insert A Γ hA ih =>
      obtain ⟨A, rfl⟩ := Quotient.exists_rep A
      obtain ⟨xs, rfl⟩ := ih
      exact ⟨A :: xs, ContextPrograms.context_cons A xs⟩
  obtain ⟨xs, rfl⟩ := contexts Γ
  exact ⟨_, LocalRulePrograms.parseSequent_encode xs φ⟩

/-- Numerical and mathematical trees have exactly the same unannotated shape. -/
inductive Represents : Data → SequentTree membershipLanguage → Prop where
  | node {n : ℕ} {s : Sequent membershipLanguage} {cs : List Data}
      {ts : List (SequentTree membershipLanguage)} :
      LocalRulePrograms.parseSequent n = some s →
      List.Forall₂ Represents cs ts → Represents (.node n cs) (.node s ts)

theorem Represents.root {D : Data} {T : SequentTree membershipLanguage}
    (h : Represents D T) : LocalRulePrograms.parseSequent D.root = some T.root := by
  cases h with
  | node hs _ => exact hs

theorem exists_representative (T : SequentTree membershipLanguage) :
    ∃ D, Represents D T := by
  cases T with
  | node s ts =>
    obtain ⟨n, hn⟩ := exists_sequent_code s
    have hc : ∀ t ∈ ts, ∃ d, Represents d t := by
      intro t ht
      exact exists_representative t
    have hl : ∃ ds, List.Forall₂ Represents ds ts := by
      clear hn
      induction ts with
      | nil => exact ⟨[], .nil⟩
      | cons t ts ih =>
        obtain ⟨d, hd⟩ := hc t (by simp)
        obtain ⟨ds, hds⟩ := ih (fun t ht => hc t (by simp [ht]))
        exact ⟨d :: ds, .cons hd hds⟩
    obtain ⟨ds, hds⟩ := hl
    exact ⟨.node n ds, .node hn hds⟩
termination_by sizeOf T
decreasing_by
  have h := List.sizeOf_lt_of_mem ht
  simp only [SequentTree.node.sizeOf_spec]
  omega

theorem Checked.exists_interpretation {D : Data} (h : Checked D) :
    ∃ T, Represents D T := by
  induction h with
  | @node n ds hn hr hc ih =>
    obtain ⟨s, hs⟩ := (LocalRulePrograms.validSequent_ne_zero Grammar.Program.ident n).mp hn
    have hl : ∃ ts, List.Forall₂ Represents ds ts := by
      clear hr hc
      induction ds with
      | nil => exact ⟨[], .nil⟩
      | cons d ds ihds =>
        obtain ⟨t, ht⟩ := ih d (by simp)
        obtain ⟨ts, hts⟩ := ihds (fun d hd => ih d (by simp [hd]))
        exact ⟨t :: ts, .cons ht hts⟩
    obtain ⟨ts, hts⟩ := hl
    exact ⟨.node s ts, .node hs hts⟩

theorem represents_roots {ds : List Data} {ts : List (SequentTree membershipLanguage)}
    (h : List.Forall₂ Represents ds ts) :
    List.Forall₂ (fun n s => LocalRulePrograms.parseSequent n = some s)
      (ds.map Data.root) (ts.map SequentTree.root) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.root ih

theorem Represents.valid_root {D : Data} {T : SequentTree membershipLanguage}
    (h : Represents D T) : validSeq D.root ≠ 0 :=
  (LocalRulePrograms.validSequent_ne_zero Grammar.Program.ident D.root).mpr ⟨T.root, h.root⟩

end PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
