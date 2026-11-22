module

public import PolishSpaceBook.BorelExpressionCertificates
public import PolishSpaceBook.PolishEmbeddingsBorelRefinements

@[expose] public section

/-!
# Uniform evaluation for Borel leaves

Refine the topology once to make the countable family of leaves clopen.
The existing closed-certificate proof then applies, and the continuous
identity map returns its analytic projections to the original topology.
-/

namespace PolishSpaceBook.BorelExpression
open Set MeasureTheory TopologicalSpace

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    By the refinement theorem in §{sec:polish-topology-refinement}, choose a finer Polish topology on $X$ making all
    $U_n$ clopen. Each certificate condition is now clopen in the code, point, truth bits, and selected subcode numbers.
    For the condition using $j_s$, fix each possible value $k$ and impose the corresponding implication.
    The conjunction of the resulting countably many conditions is closed. Requiring the bit at the empty position to be
    $1$ or $0$
    still gives a closed relation. Its two projections onto the code and point coordinates are analytic.
    The identity map from the refined product to the original product is continuous, so these same sets, denoted by
    $V$ and $F$, are analytic in the original topology too.
-/
/-- The uniform truth and falsity predicates remain analytic for arbitrary
Borel leaves; validity is not a precondition on their domain. -/
theorem analyticSet_evaluationSide_of_measurable {X : Type*}
    [t : TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (b : Bool) :
    AnalyticSet (EvaluationSide U b) := by
  obtain ⟨t', hle, hp, _, hcl⟩ := exists_polish_refinement_clopen U hU
  let : TopologicalSpace X := t'
  let : PolishSpace X := hp
  have ha := analyticSet_evaluationSide U hcl b
  have hf : @Continuous (BorelExpression × X) (BorelExpression × X)
      inferInstance (@instTopologicalSpaceProd BorelExpression X inferInstance t) id :=
    continuous_id_of_le (TopologicalSpace.prod_mono le_rfl hle)
  have h := @AnalyticSet.image_of_continuous (BorelExpression × X) inferInstance
    (BorelExpression × X) (@instTopologicalSpaceProd BorelExpression X inferInstance t)
    _ ha id hf
  simpa only [image_id] using h

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: proposition
  title: Uniform evaluation of Borel codes
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    For a valid code, induction on immediate subcodes gives a unique rule-obeying truth assignment.
    Choosing a true subcode at every true union position extends it to a certificate.
    Conversely, the local rules force every certificate to have exactly this truth assignment.
    Its bit at the empty position is $1$ exactly when $x\in A_c$, and is $0$ exactly when $x\notin A_c$.
    This proves the two equivalences.
-/
/-- Two ambient analytic sets give complementary descriptions on valid codes.
No assertion that the restricted domain is Borel is needed. -/
theorem exists_analytic_evaluation_pair {X : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) :
    ∃ V F : Set (BorelExpression × X), AnalyticSet V ∧ AnalyticSet F ∧
      ∀ c (hc : c.Valid) x,
        ((c, x) ∈ V ↔ x ∈ c.evaluate hc.2.2.2.2.2 U []) ∧
        ((c, x) ∉ F ↔ x ∈ c.evaluate hc.2.2.2.2.2 U []) := by
  refine ⟨EvaluationSide U true, EvaluationSide U false,
    analyticSet_evaluationSide_of_measurable U hU true,
    analyticSet_evaluationSide_of_measurable U hU false, ?_⟩
  intro c hc x
  exact ⟨evaluationSide_iff_mem U c hc x,
    (evaluationSides_complementary U c hc x).symm.trans (evaluationSide_iff_mem U c hc x)⟩

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The \termdefine{decoding relation} is
    $$D := \{(c, x) : c \in \BorelCodes,\, x \in A_c\}.$$
    The following uniform descriptions distinguish evaluation on valid codes from a statement about all real parameters.
-/
/-- Evaluation restricted to valid codes, as a subset of the ambient product. -/
def DecodingRelation {X : Type*} (U : ℕ → Set X) : Set (BorelExpression × X) :=
  {p | ∃ hc : p.1.Valid, p.2 ∈ p.1.evaluate hc.2.2.2.2.2 U []}

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The descriptions $V$ and $F^c$ agree on valid codes.
-/
/-- The analytic truth and coanalytic falsity descriptions agree on valid codes.
The validity restriction is retained; no ambient Borel conclusion is asserted. -/
theorem decodingRelation_eq_restricted_evaluation {X : Type*} (U : ℕ → Set X) :
    DecodingRelation U = {p | p.1.Valid} ∩ EvaluationSide U true ∧
    DecodingRelation U = {p | p.1.Valid} ∩ Coevaluation U := by
  constructor
  · ext p
    constructor
    · rintro ⟨hc, hx⟩
      exact ⟨hc, (evaluationSide_iff_mem U p.1 hc p.2).mpr hx⟩
    · rintro ⟨hc, hx⟩
      exact ⟨hc, (evaluationSide_iff_mem U p.1 hc p.2).mp hx⟩
  · ext p
    constructor
    · rintro ⟨hc, hx⟩
      exact ⟨hc, (coevaluation_eq_evaluation_on_valid U p.1 hc p.2).mpr
        ((evaluationSide_iff_mem U p.1 hc p.2).mpr hx)⟩
    · rintro ⟨hc, hx⟩
      exact ⟨hc, (evaluationSide_iff_mem U p.1 hc p.2).mp
        ((coevaluation_eq_evaluation_on_valid U p.1 hc p.2).mp hx)⟩

end PolishSpaceBook.BorelExpression
