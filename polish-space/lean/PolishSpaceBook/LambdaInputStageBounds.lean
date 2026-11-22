module

public import PolishSpaceBook.LambdaFiniteTrials

@[expose] public section

/-! # The stage number bounds all input addresses

The paired-successor list encoding bounds each entry by the list code. Thus a
stage-s certificate search never needs input coordinates at or beyond s.
-/
namespace PolishSpaceBook.NamedLambda
namespace Term

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The empty table has bound and code zero. If its first entry is $(i,v)$ and its tail has code $d$,
    its code is $\NatPair{\NatPair{i}{v}}{d}+1$. Each numerical projection is at most the paired number.
    Thus $i+1$ is at most this code, and the induction hypothesis bounds the tail's addresses by $d$,
    which is smaller than the whole code. Taking the maximum proves the table inequality.
    The table code of candidate $s$ is at most $s$. Induction in
    $H(s+1)=\max(H(s),K(t_s))$ therefore gives $H(s+1)\le s+1$.
    Apply the preceding input-agreement lemma with this bound.
    \end{proof}
-/
theorem answerBound_decode_le (e : ℕ) : answerBound (decodeAnswerTable e) ≤ e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simp [decodeAnswerTable,NatListCode.decode,answerBound]
    | succ e =>
      have ht := ih e.unpair.2 (by have := Nat.unpair_right_le e; omega)
      have hh := (Nat.unpair_left_le e.unpair.1).trans (Nat.unpair_left_le e)
      have hd := Nat.unpair_right_le e
      simp only [decodeAnswerTable,NatListCode.decode,List.map_cons,answerBound]
      exact max_le (by omega) (ht.trans (by omega))

theorem answerBound_le_code (t : AnswerTable) : answerBound t ≤ answerTableCode t := by
  simpa only [decode_answerTableCode] using answerBound_decode_le (answerTableCode t)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The empty table has bound and code zero. If its first entry is $(i,v)$ and its tail has code $d$,
    its code is $\NatPair{\NatPair{i}{v}}{d}+1$. Each numerical projection is at most the paired number.
    Thus $i+1$ is at most this code, and the induction hypothesis bounds the tail's addresses by $d$,
    which is smaller than the whole code. Taking the maximum proves the table inequality.
    The table code of candidate $s$ is at most $s$. Induction in
    $H(s+1)=\max(H(s),K(t_s))$ therefore gives $H(s+1)\le s+1$.
    Apply the preceding input-agreement lemma with this bound.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Stage address bound
-/
theorem inputTestBound_le (s : ℕ) : inputTestBound s ≤ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have ht := (answerBound_decode_le s.unpair.1).trans (Nat.unpair_left_le s)
    exact max_le (by omega) (by omega)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The empty table has bound and code zero. If its first entry is $(i,v)$ and its tail has code $d$,
    its code is $\NatPair{\NatPair{i}{v}}{d}+1$. Each numerical projection is at most the paired number.
    Thus $i+1$ is at most this code, and the induction hypothesis bounds the tail's addresses by $d$,
    which is smaller than the whole code. Taking the maximum proves the table inequality.
    The table code of candidate $s$ is at most $s$. Induction in
    $H(s+1)=\max(H(s),K(t_s))$ therefore gives $H(s+1)\le s+1$.
    Apply the preceding input-agreement lemma with this bound.
    \end{proof}
-/
theorem boundedInputTest_eq_of_stage_prefix {p q : ℕ → ℕ} (M N : Term) (s : ℕ)
    (h : ∀ i < s, q i = p i) :
    boundedInputTest q M N s = boundedInputTest p M N s :=
  boundedInputTest_eq_of_prefix M N s (fun i hi => h i (hi.trans_le (inputTestBound_le s)))

end Term
namespace AlphaTerm

theorem finiteTrial_eq_of_stage_prefix {p q : ℕ → ℕ} (e n k : ℕ)
    (h : ∀ i < k.unpair.2, q i = p i) :
    Term.finiteTrial q e n k = Term.finiteTrial p e n k :=
  finiteTrial_eq_of_prefix e n k (fun i hi => h i (hi.trans_le (Term.inputTestBound_le _)))

end AlphaTerm
end PolishSpaceBook.NamedLambda
