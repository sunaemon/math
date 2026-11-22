module

public import PolishSpaceBook.LambdaNumericalFunctions

@[expose] public section

/-! # The Y combinator and its actual common reduct, including open arguments -/

namespace PolishSpaceBook.NamedLambda.AlphaTerm

def selfApplicationBody (x : ℕ) (F : AlphaTerm) : AlphaTerm :=
  lam x (app F (app (var x) (var x)))

theorem selfApplicationBody_rename (F : AlphaTerm) (x y : ℕ)
    (hx : x ∉ F.fv) (hy : y ∉ F.fv) : selfApplicationBody x F = selfApplicationBody y F := by
  by_cases hxy : x = y
  · exact hxy ▸ rfl
  · unfold selfApplicationBody
    rw [lam_rename _ x y (by simp [fv_app, fv_var, hy, Ne.symm hxy])]
    simp only [subst_app, subst_var, ite_true, subst_not_free F (var y) x hx]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Lambda terms also admit a fixed-point combinator
        $$\mathsf Y := \lambdaab{f}{(\lambdaab{x}{f(xx)})(\lambdaab{x}{f(xx)})}.$$
        It satisfies $\BetaConvertible{\mathsf Y F}{F(\mathsf Y F)}$. This is not a one-step reduction identity: with
        $A=\lambdaab{x}{F(xx)}$, both sides reduce to $F(AA)$.
-/
def yCombinator : AlphaTerm :=
  lam 0 (app (selfApplicationBody 1 (var 0)) (selfApplicationBody 1 (var 0)))

theorem yCombinator_closed : yCombinator.Closed := by
  simp [yCombinator, selfApplicationBody, Closed, fv_lam, fv_app, fv_var]
  decide

theorem yCombinator_start (F : AlphaTerm) (x : ℕ) (hx : x ∉ F.fv) (hx0 : x ≠ 0) :
    Beta (app yCombinator F) (app (selfApplicationBody x F) (selfApplicationBody x F)) := by
  have he : selfApplicationBody 1 (var 0) = selfApplicationBody x (var 0) :=
    selfApplicationBody_rename (var 0) 1 x (by simp [fv_var]) (by simpa [fv_var] using hx0)
  have hs : (selfApplicationBody x (var 0)).subst 0 F = selfApplicationBody x F := by
    rw [selfApplicationBody, subst_lam_fresh _ _ x 0 hx0 hx]
    simp [selfApplicationBody, subst_app, subst_var, hx0]
  unfold yCombinator
  rw [he]
  simpa only [subst_app, hs] using
    Beta.contract 0 (app (selfApplicationBody x (var 0)) (selfApplicationBody x (var 0))) F

theorem selfApplicationBody_contract (F : AlphaTerm) (x : ℕ) (hx : x ∉ F.fv) :
    Beta (app (selfApplicationBody x F) (selfApplicationBody x F))
      (app F (app (selfApplicationBody x F) (selfApplicationBody x F))) := by
  change Beta (app (lam x (app F (app (var x) (var x)))) (selfApplicationBody x F)) _
  simpa only [subst_app, subst_var, ite_true, subst_not_free F _ x hx] using
    Beta.contract x (app F (app (var x) (var x))) (selfApplicationBody x F)

/-- Both sides reach F(A A); the fixed-point equation asserts beta-convertibility. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Lambda terms also admit a fixed-point combinator
        $$\mathsf Y := \lambdaab{f}{(\lambdaab{x}{f(xx)})(\lambdaab{x}{f(xx)})}.$$
        It satisfies $\BetaConvertible{\mathsf Y F}{F(\mathsf Y F)}$. This is not a one-step reduction identity: with
        $A=\lambdaab{x}{F(xx)}$, both sides reduce to $F(AA)$.
-/
theorem yCombinator_convertible (F : AlphaTerm) :
    Relation.EqvGen Beta (app yCombinator F) (app F (app yCombinator F)) := by
  obtain ⟨x, hx⟩ := Term.exists_fresh (F.fv ∪ {0})
  have hxf : x ∉ F.fv := fun h => hx (Finset.mem_union_left _ h)
  have hx0 : x ≠ 0 := fun h => hx (Finset.mem_union_right _ (by simp [h]))
  have hb := yCombinator_start F x hxf hx0
  exact church_rosser.mpr ⟨_, .tail (.single hb) (selfApplicationBody_contract F x hxf),
    .single (.app_right F hb)⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
