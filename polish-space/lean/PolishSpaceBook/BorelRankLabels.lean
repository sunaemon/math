module

public import PolishSpaceBook.BorelRankApproximations

@[expose] public section

/-! # Finite word labels for the rank-layer construction

Every recursive label query consumes five word entries. The definition makes
sense without well-foundedness of the bound relation; well-foundedness is used
to prove validity and the rank interpretation, not to terminate a label query.
This structural description is not an alternative computation model.
-/
namespace PolishSpaceBook
open BorelExpression
namespace RankBound

/-- The raw Boolean expansion of one rank-recursion clause. -/
def rawStep (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (rec : ℕ → ℕ → BorelExpression) (a s : ℕ) : BorelExpression :=
  complement (union (fun t => complement (union (fun j =>
    if j = 0 then complement (E t s) else
      union (fun b => if R b a then rec b t else complement (basic 0))))))

/-- Reading a finite address requires only a finite number of lower-bound tests. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The well-founded recursion also has a description at finite word addresses. Its fixed initial labels are
    $$\begin{array}{c|ccccc}
    w&\emptySeq&(0)&(0,t)&(0,t,0)&(0,t,0,0)\\\hline
    \RankLayerCode{a}{s}(w)&2&1&2&1&2.
    \end{array}$$
    The other potentially nonzero labels are
    $$\begin{aligned}
    \RankLayerCode{a}{s}((0,t,0,0,0)\concat v)&=e_{t,s}(v),\\
    \RankLayerCode{a}{s}((0,t,0,j))&=1\quad(j>0),\\
    \RankLayerCode{a}{s}((0,t,0,j,b)\concat v)&=
     \begin{cases}\RankLayerCode{b}{t}(v)&R(b,a),\\
                   \BorelEmptyCode(v)&\neg R(b,a)\end{cases}\quad(j>0).
    \end{aligned}$$
    All remaining labels are zero. These equations specify a label map even for a relation $R$ that is
    not well founded: each call to another rank-layer label consumes five entries of the address.
    Well-foundedness of $R$ is needed for validity and the rank interpretation, not for this finite-word recursion.
-/
def labels (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (a s : ℕ) : BorelExpression
  | [] => 2
  | [0] => 1
  | [0,_t] => 2
  | [0,_t,0] => 1
  | [0,_t,0,0] => 2
  | 0 :: t :: 0 :: 0 :: 0 :: w => E t s w
  | [0,_t,0,_j+1] => 1
  | 0 :: t :: 0 :: (_j+1) :: b :: w =>
      if R b a then labels E R b t w else complement (basic 0) w
  | _ => 0
termination_by structural w => w

theorem labels_eq (E : ℕ → ℕ → BorelExpression) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (a s : ℕ) : labels E R a s = rawStep E R (labels E R) a s := by
  funext w
  rcases w with _ | ⟨i,w⟩
  · rfl
  cases i with
  | succ i => simp [labels,rawStep,complement,graft,absent]
  | zero =>
    rcases w with _ | ⟨t,w⟩
    · rfl
    rcases w with _ | ⟨i,w⟩
    · rfl
    cases i with
    | succ i => simp [labels,rawStep,complement,union,graft,absent]
    | zero =>
      rcases w with _ | ⟨j,w⟩
      · rfl
      cases j with
      | zero =>
        rcases w with _ | ⟨i,w⟩
        · rfl
        cases i <;> simp [labels,rawStep,complement,union,graft,absent]
      | succ j =>
        rcases w with _ | ⟨b,w⟩
        · rfl
        by_cases h : R b a <;> simp [labels,rawStep,complement,union,graft,h]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Finite labels of rank expressions
  excerpt: |
    For well-founded $R$, the finite-word equations give exactly the label map of $\RankLayerCode{a}{s}$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Expand the countable intersection as complement, union, complement. Its first three labels are
    $2,1,2$ at the displayed addresses. The binary union adds label $1$. At its child zero, a complement
    adds label $2$ and its child zero enters $e_{t,s}$. At each other child, the union over $b$ adds label
    $1$, then selects the lower expression or the empty-set expression according to $R(b,a)$.
    Every forbidden child of a complement is absent. This is precisely the displayed list of cases.
    Induction on $R$, for all finite addresses at once, identifies the recursive calls with the corresponding
    lower expressions. Thus the two label maps agree.
-/
theorem code_val_eq_labels (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (hR : WellFounded R) (a s : ℕ) :
    (code E R hR a s).val = labels (fun t s => (E t s).val) R a s := by
  classical
  induction a using hR.induction generalizing s with
  | h a ih =>
    rw [code_eq,labels_eq]
    simp only [codeStep,Code.iInter,Code.iUnion,Code.compl,Code.sup,Code.empty,Code.leaf]
    simp only [apply_ite,apply_dite]
    unfold rawStep
    apply congrArg complement
    apply congrArg union
    funext t
    apply congrArg complement
    apply congrArg union
    funext j
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj,ite_false]
      apply congrArg union
      funext b
      by_cases hb : R b a
      · simp [hb,ih b hb t]
      · simp [hb]


theorem labels_valid (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (hR : WellFounded R) (a s : ℕ) :
    (labels (fun t s => (E t s).val) R a s).Valid := by
  rw [← code_val_eq_labels E R hR a s]
  exact (code E R hR a s).property


end RankBound
end PolishSpaceBook
