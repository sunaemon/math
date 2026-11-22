module

public import PolishSpaceBook.BorelExpressionEvaluation
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Uniform closed certificates for Borel expression evaluation

The label tree is a variable in the closed certificate relation, so its
projections are uniform analytic truth and falsity predicates, even on
invalid inputs. On valid trees uniqueness makes these predicates
complementary. This is the topological part of the coding argument; the
relative recursive tree presentation is not yet asserted here.
-/

namespace PolishSpaceBook
namespace BorelExpression
open Set MeasureTheory

abbrev CertificatePoint (X : Type*) :=
  (BorelExpression × X) × ((List ℕ → Bool) × (List ℕ → ℕ))

private theorem clopen_imp {Z : Type*} [TopologicalSpace Z] {p q : Z → Prop}
    (hp : IsClopen {z | p z}) (hq : IsClopen {z | q z}) : IsClopen {z | p z → q z} := by
  convert hp.compl.union hq using 1
  ext z
  simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]

private theorem clopen_iff {Z : Type*} [TopologicalSpace Z] {p q : Z → Prop}
    (hp : IsClopen {z | p z}) (hq : IsClopen {z | q z}) : IsClopen {z | p z ↔ q z} := by
  simpa only [iff_iff_implies_and_implies, ofPred_and] using
    (clopen_imp hp hq).inter (clopen_imp hq hp)

private theorem closed_forall {Z I : Type*} [TopologicalSpace Z] {p : I → Z → Prop}
    (h : ∀ i, IsClosed {z | p i z}) : IsClosed {z | ∀ i, p i z} := by
  simpa only [ofPred_forall] using isClosed_iInter h

/-- Only finitely many discrete coordinates occur in each local clause.
Taking their intersection gives a closed relation uniformly in the code. -/
theorem isClosed_localCertificate {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : ∀ n, IsClopen (U n)) :
    IsClosed {z : CertificatePoint X | z.1.1.LocalCertificate U z.1.2 z.2.1 z.2.2} := by
  have hc (s : List ℕ) (n : ℕ) : IsClopen {z : CertificatePoint X | z.1.1 s = n} :=
    (isClopen_discrete {n}).preimage (by fun_prop)
  have hv (s : List ℕ) (b : Bool) : IsClopen {z : CertificatePoint X | z.2.1 s = b} :=
    (isClopen_discrete {b}).preimage (by fun_prop)
  have hi (s : List ℕ) (n : ℕ) : IsClopen {z : CertificatePoint X | z.2.2 s = n} :=
    (isClopen_discrete {n}).preimage (by fun_prop)
  have hn (s t : List ℕ) : IsClopen {z : CertificatePoint X | z.2.1 s = !z.2.1 t} :=
    (isClopen_discrete {p : Bool × Bool | p.1 = !p.2}).preimage
      (show Continuous (fun z : CertificatePoint X => (z.2.1 s, z.2.1 t)) by fun_prop)
  apply closed_forall
  intro s
  refine (clopen_imp (hc s 0) (hv s false)).isClosed.inter ?_
  refine (closed_forall (fun k => (clopen_imp (hc s 1) (clopen_imp (hv s true)
    (clopen_imp (hi s k) ((hc (s ++ [k]) 0).compl.inter (hv (s ++ [k]) true))))).isClosed)).inter ?_
  refine (closed_forall (fun k => (clopen_imp (hc s 1) (clopen_imp (hc (s ++ [k]) 0).compl
    (clopen_imp (hv (s ++ [k]) true) (hv s true)))).isClosed)).inter ?_
  refine (closed_forall (fun k => (clopen_imp (hc s 2) (clopen_imp (hc (s ++ [k]) 0).compl
    (hn s (s ++ [k])))).isClosed)).inter ?_
  exact closed_forall (fun n => (clopen_imp (hc s (n + 3))
    (clopen_iff (hv s true) ((hU n).preimage (by fun_prop)))).isClosed)

theorem isClosed_evaluationCertificate {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : ∀ n, IsClopen (U n)) :
    IsClosed {z : CertificatePoint X | z.1.1.EvaluationCertificate U z.1.2 z.2.1 z.2.2} := by
  simpa only [certificate_iff_local] using isClosed_localCertificate U hU

/-- Two uniform predicates are obtained by specifying the root truth bit.
They are defined on all external codes, without a validity precondition. -/
def EvaluationSide {X : Type*} (U : ℕ → Set X) (b : Bool) : Set (BorelExpression × X) :=
  {p | ∃ v choice, p.1.EvaluationCertificate U p.2 v choice ∧ v [] = b}

theorem analyticSet_evaluationSide {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (U : ℕ → Set X) (hU : ∀ n, IsClopen (U n)) (b : Bool) :
    AnalyticSet (EvaluationSide U b) := by
  let : PolishSpace Bool := inferInstance
  let S := {z : CertificatePoint X | z.1.1.EvaluationCertificate U z.1.2 z.2.1 z.2.2 ∧ z.2.1 [] = b}
  have hs : IsClosed S := (isClosed_evaluationCertificate U hU).inter
    ((isClopen_discrete {b}).preimage (by fun_prop)).isClosed
  have heq : Prod.fst '' S = EvaluationSide U b := by
    ext p
    constructor
    · rintro ⟨⟨p, v, choice⟩, h, rfl⟩
      exact ⟨v, choice, h⟩
    · rintro ⟨v, choice, h⟩
      exact ⟨(p, v, choice), h, rfl⟩
  rw [← heq]
  exact hs.analyticSet.image_of_continuous continuous_fst

theorem evaluationSide_iff_mem {X : Type*} (U : ℕ → Set X)
    (c : BorelExpression) (hc : c.Valid) (x : X) :
    (c, x) ∈ EvaluationSide U true ↔ x ∈ c.evaluate hc.2.2.2.2.2 U [] := by
  classical
  rw [show (c, x) ∈ EvaluationSide U true ↔
      (∃ v choice, c.EvaluationCertificate U x v choice ∧ v [] = true) from Iff.rfl,
    c.certificate_root_iff hc]
  simp [truthValues]

/-- On a valid tree the positive evaluation is the complement of the
negative evaluation. No conclusion of this form is made for invalid trees. -/
theorem evaluationSides_complementary {X : Type*} (U : ℕ → Set X)
    (c : BorelExpression) (hc : c.Valid) (x : X) :
    (c, x) ∈ EvaluationSide U true ↔ (c, x) ∉ EvaluationSide U false := by
  change (∃ v choice, c.EvaluationCertificate U x v choice ∧ v [] = true) ↔
    ¬ (∃ v choice, c.EvaluationCertificate U x v choice ∧ v [] = false)
  rw [c.certificate_root_iff hc, c.certificate_root_iff hc]
  cases c.truthValues hc.2.2.2.2.2 U x [] <;> simp

/-- The book's coanalytic evaluation W is the complement of the analytic
falsity predicate; it agrees with analytic truth V at every valid code. -/
def Coevaluation {X : Type*} (U : ℕ → Set X) : Set (BorelExpression × X) :=
  (EvaluationSide U false)ᶜ

theorem coevaluation_eq_evaluation_on_valid {X : Type*} (U : ℕ → Set X)
    (c : BorelExpression) (hc : c.Valid) (x : X) :
    (c, x) ∈ Coevaluation U ↔ (c, x) ∈ EvaluationSide U true :=
  (evaluationSides_complementary U c hc x).symm

end BorelExpression
end PolishSpaceBook
