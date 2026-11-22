module

public import PolishSpaceBook.LambdaListPrefixes
public import PolishSpaceBook.LambdaRelativeComposition
public import PolishSpaceBook.LambdaNumericalQueries

@[expose] public section

/-! # One predicate program for every input parameter

Uniformity is outside the parameter quantifier: there exists one closed term,
not a separately chosen decision program for each input sequence.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
universe u v

def UniformDecidablePredicate {α : Type u} [Encodable α]
    (R : (ℕ → ℕ) → α → Prop) : Prop := ∃ P, ∀ p, Decides p P (R p)

namespace UniformDecidablePredicate

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem not {α : Type u} [Encodable α] {R : (ℕ → ℕ) → α → Prop}
    (hR : UniformDecidablePredicate R) : UniformDecidablePredicate (fun p a => ¬ R p a) := by
  obtain ⟨P,hP⟩ := hR
  refine ⟨mapOutputProgram reverseZeroTerm P,fun p =>
    ⟨mapOutputProgram_closed reverseZero_computes.1 (hP p).1,fun a => ⟨?_,?_⟩⟩⟩
  · intro h
    simpa using mapOutputProgram_runs reverseZero_computes.1 (hP p).1
      (((hP p).2 a).2 h) (reverseZero_computes.2 0)
  · intro h
    simpa using mapOutputProgram_runs reverseZero_computes.1 (hP p).1
      (((hP p).2 a).1 (not_not.mp h)) (reverseZero_computes.2 1)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem and {α : Type u} [Encodable α] {R S : (ℕ → ℕ) → α → Prop}
    (hR : UniformDecidablePredicate R) (hS : UniformDecidablePredicate S) :
    UniformDecidablePredicate (fun p a => R p a ∧ S p a) := by
  classical
  obtain ⟨P,hP⟩ := hR
  obtain ⟨Q,hQ⟩ := hS
  let M := mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false)
  have hM : NumericalComputes M (fun z => z.unpair.1 * z.unpair.2) :=
    (projection_computes true).mul (projection_computes false)
  refine ⟨mapOutputProgram M (pairOutputProgram P Q),fun p =>
    ⟨mapOutputProgram_closed hM.1 (pairOutputProgram_closed (hP p).1 (hQ p).1),fun a => ?_⟩⟩
  have hr := mapOutputProgram_runs hM.1 (pairOutputProgram_closed (hP p).1 (hQ p).1)
    (pairOutputProgram_runs (hP p).1 (hQ p).1 ((hP p).runs a) ((hQ p).runs a))
    (hM.2 (Nat.pair (if R p a then 1 else 0) (if S p a then 1 else 0)))
  simp only [Nat.unpair_pair] at hr
  constructor
  · rintro ⟨ha,hb⟩; simpa only [ite_eq_left ha,ite_eq_left hb,mul_one] using hr
  · intro h
    by_cases ha : R p a
    · have hb : ¬ S p a := fun hb => h ⟨ha,hb⟩
      simpa only [ite_eq_left ha,ite_eq_right hb,mul_zero] using hr
    · simpa only [ite_eq_right ha,zero_mul] using hr

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem or {α : Type u} [Encodable α] {R S : (ℕ → ℕ) → α → Prop}
    (hR : UniformDecidablePredicate R) (hS : UniformDecidablePredicate S) :
    UniformDecidablePredicate (fun p a => R p a ∨ S p a) := by
  simpa only [not_and_or,not_not] using (hR.not.and hS.not).not

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem imp {α : Type u} [Encodable α] {R S : (ℕ → ℕ) → α → Prop}
    (hR : UniformDecidablePredicate R) (hS : UniformDecidablePredicate S) :
    UniformDecidablePredicate (fun p a => R p a → S p a) := by
  simpa only [imp_iff_not_or] using hR.not.or hS

theorem precompNumerical {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    {F : AlphaTerm} {f : ℕ → ℕ} {g : α → β} {R : (ℕ → ℕ) → β → Prop}
    (hR : UniformDecidablePredicate R) (hF : NumericalComputes F f)
    (hf : ∀ a, f (Encodable.encode a) = Encodable.encode (g a)) :
    UniformDecidablePredicate (fun p a => R p (g a)) := by
  obtain ⟨P,hP⟩ := hR
  exact ⟨reindexProgram P F,fun p => (hP p).precompNumerical hF hf⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem eq {F G : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hf : UniformNumericalComputes F f) (hg : UniformNumericalComputes G g) :
    UniformDecidablePredicate (fun p n => f p n = g p n) := by
  classical
  have h := hf.combine hg equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  refine ⟨_,fun p => ⟨h.1,fun n => ⟨?_,?_⟩⟩⟩ <;> intro hn
  · simpa [hn] using h.2 p n
  · simpa [hn] using h.2 p n

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
    of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
    $$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
    In the preceding syntax-row program replace $\LambdaTermName{labelAt}(o,e,w)$ by
    $\LambdaTermName{streamLabels}ow$, omit the unused family index, and
    use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
    Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
    implication are obtained from these operations. Each operation combines fixed closed terms, so the
    result is one program for all input names. It does not choose a new term after receiving a name.
-/
theorem le {F G : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hf : UniformNumericalComputes F f) (hg : UniformNumericalComputes G g) :
    UniformDecidablePredicate (fun p n => f p n ≤ g p n) := by
  classical
  have hc := (projection_computes true).ifLe (projection_computes false)
    (numericalConstant_computes 1) (numericalConstant_computes 0)
  have h := (hf.pair hg).map hc
  refine ⟨_,fun p => ⟨h.1,fun n => ⟨?_,?_⟩⟩⟩ <;> intro hn
  · simpa [Nat.unpair_pair,hn] using h.2 p n
  · simpa [Nat.unpair_pair,hn] using h.2 p n

end UniformDecidablePredicate
end LambdaRelative
namespace NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem UniformNumericalComputes.comp {P Q : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hP : UniformNumericalComputes P f) (hQ : UniformNumericalComputes Q g) :
    UniformNumericalComputes (relativeComposeProgram P Q) (fun p n => f p (g p n)) :=
  ⟨relativeComposeProgram_closed hP.1 hQ.1,
    fun p n => relativeComposeProgram_runs hP.1 hQ.1 (hQ.2 p n) (hP.2 p (g p n))⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
    Numerical projections
    supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
    and numerical
    composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
    test with those
    arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
    the claimed output from every successful trial; completeness provides a bound for every genuine
    output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
    Hence the inverse
    image, intersection, projection, and union operations in the main proof all use closed lambda terms
    at the original parameter. The only choices of entire tables occur in the proof of their existence.
-/
theorem UniformNumericalComputes.changeInput {P Q : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hP : UniformNumericalComputes P f) (hQ : UniformNumericalComputes Q g) :
    UniformNumericalComputes (compositionProgram P Q) (fun p n => f (g p) n) :=
  ⟨compositionProgram_closed hP.1 hQ.1,
    fun p n => compositionProgram_runs hP.1 hQ.1 (hP.2 (g p) n) (hQ.2 p)⟩

end NamedLambda.AlphaTerm
end PolishSpaceBook
