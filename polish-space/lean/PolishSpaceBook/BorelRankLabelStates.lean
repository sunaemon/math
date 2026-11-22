module

public import PolishSpaceBook.BorelRankLabels

@[expose] public section

/-! # Numerical states for finite rank-label evaluation

A state stores either a completed label, or the two indices and remaining finite
word. These are data for iteration by a Church numeral, not a new programming
language. Every nonterminal update consumes five word entries.
-/
namespace PolishSpaceBook
open BorelExpression NamedLambda
namespace RankBound

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the rank-label program, let $P$ compute the edge label $e_{t,s}(v)$ from
    $\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$, and let $Q$ decide $R(b,a)$ from
    $\NatPair{b}{a}$, returning one for truth and zero for falsity. Both must be total at the fixed
    parameter. The desired labels obey the finite-word equations in §{sec:edst-borel-rank-layers}.
    Labels zero, one, and two mean absence, union, and complement; a leaf for the whole space has label three.
    Use the numerical states
    $$d(m):=\NatPair{0}{m},\qquad
    q(a,s,v):=\NatPair{1}{\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}}.$$
    The first is finished; the second requests a rank label. These states are numerical data for lambda terms.
-/
def doneState (r : ℕ) : ℕ := Nat.pair 0 r

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the rank-label program, let $P$ compute the edge label $e_{t,s}(v)$ from
    $\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$, and let $Q$ decide $R(b,a)$ from
    $\NatPair{b}{a}$, returning one for truth and zero for falsity. Both must be total at the fixed
    parameter. The desired labels obey the finite-word equations in §{sec:edst-borel-rank-layers}.
    Labels zero, one, and two mean absence, union, and complement; a leaf for the whole space has label three.
    Use the numerical states
    $$d(m):=\NatPair{0}{m},\qquad
    q(a,s,v):=\NatPair{1}{\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}}.$$
    The first is finished; the second requests a rank label. These states are numerical data for lambda terms.
-/
def queryState (a s : ℕ) (w : List ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair a (Nat.pair s (NatListCode.encode w)))

def update (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (a s : ℕ) : List ℕ → ℕ
  | [] => doneState 2
  | [0] => doneState 1
  | [0,_t] => doneState 2
  | [0,_t,0] => doneState 1
  | [0,_t,0,0] => doneState 2
  | 0 :: t :: 0 :: 0 :: 0 :: w => doneState (E t s w)
  | [0,_t,0,_j+1] => doneState 1
  | 0 :: t :: 0 :: (_j+1) :: b :: w =>
      if R b a then queryState b t w else doneState (complement (basic 0) w)
  | _ => doneState 0

def stateStep (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (z : ℕ) : ℕ :=
  if z.unpair.1 = 0 then z else
    update E R z.unpair.2.unpair.1 z.unpair.2.unpair.2.unpair.1
      (NatListCode.decode z.unpair.2.unpair.2.unpair.2)

@[simp] theorem stateStep_done (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (r : ℕ) : stateStep E R (doneState r) = doneState r := by simp [stateStep,doneState]

@[simp] theorem stateStep_query (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (a s : ℕ) (w : List ℕ) : stateStep E R (queryState a s w) = update E R a s w := by
  simp [stateStep,queryState]

@[simp] theorem iterate_done (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (r n : ℕ) : ((stateStep E R)^[n]) (doneState r) = doneState r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,stateStep_done,ih]

theorem iterate_query (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (a s : ℕ) (w : List ℕ) (n : ℕ) (hn : w.length < n) :
    ((stateStep E R)^[n]) (queryState a s w) = doneState (labels E R a s w) := by
  induction n generalizing a s w with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ_apply,stateStep_query]
    rcases w with _ | ⟨i,w⟩
    · simp [update,labels]
    cases i with
    | succ i => simp [update,labels]
    | zero =>
      rcases w with _ | ⟨t,w⟩
      · simp [update,labels]
      rcases w with _ | ⟨i,w⟩
      · simp [update,labels]
      cases i with
      | succ i => simp [update,labels]
      | zero =>
        rcases w with _ | ⟨j,w⟩
        · simp [update,labels]
        cases j with
        | zero =>
          rcases w with _ | ⟨i,w⟩
          · simp [update,labels]
          cases i <;> simp [update,labels]
        | succ j =>
          rcases w with _ | ⟨b,w⟩
          · simp [update,labels]
          by_cases h : R b a
          · simp only [update,labels,h,ite_true]
            apply ih
            simp only [List.length_cons] at hn
            omega
          · simp [update,labels,h]

end RankBound
end PolishSpaceBook
