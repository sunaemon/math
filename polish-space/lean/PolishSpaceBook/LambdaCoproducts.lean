module

public import PolishSpaceBook.LambdaRealizers
public import PolishSpaceBook.RepresentedCoproducts
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Lambda realizers for tagged coproducts -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Write $\NameTail{p}(n):=p(n+1)$ for the tail of a name. Use the usual closed Church-numeral terms: successor $\LambdaSucc$ sends $n$ to $n+1$, predecessor $\LambdaPred$ sends zero to zero and $n+1$ to $n$, and $\LambdaZeroTest$ chooses the first of its two branches at zero and the second at a positive numeral. The calculations in §{sec:lambda-numeral-operations} verify these familiar operations. Define
    $$\begin{aligned}
    \LambdaNameTail&:=\lambdaab{a}{\lambdaab{b}{a(\LambdaSucc\,b)}},\\
    \LambdaNamePrefix{t}&:=\lambdaab{a}{\lambdaab{b}{
    \LambdaZeroTest\,b\,\ChurchNumeral{t}\,\bigl(a(\LambdaPred\,b)\bigr)}}\qquad(t\in\NN).
    \end{aligned}$$
    The first term removes the initial digit; the second prefixes the fixed tag $t$.
-/
def tailProgram : AlphaTerm := lam 1 (lam 2 (app (var 1) (app successorTerm (var 2))))

@[simp] theorem tailProgram_closed : tailProgram.Closed := by
  unfold Closed tailProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [successorTerm_closed]
  decide

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    For the tail term, two beta steps expose $o(\LambdaSucc\,\ChurchNumeral{n})$. Successor reduces the query argument to $\ChurchNumeral{n+1}$, and one query returns $\ChurchNumeral{p(n+1)}$. For prefixing, two beta steps expose the zero test of the output coordinate. At coordinate zero it selects $\ChurchNumeral{t}$ without evaluating the query branch. At coordinate $n+1$ it selects $o(\LambdaPred\,\ChurchNumeral{n+1})$; predecessor returns $\ChurchNumeral{n}$, and one query gives $\ChurchNumeral{p(n)}$. These calculations cover coordinate zero and every successor coordinate. Both terms are closed, and confluence excludes other numeral outputs.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Prefixing and removing a tag
-/
theorem tailProgram_runs (p : ℕ → ℕ) (n : ℕ) : OracleRuns p tailProgram n (typeTwoTailName p n) := by
  have h₁ : Beta (app tailProgram (var 0)) (lam 2 (app (var 0) (app successorTerm (var 2)))) := by
    convert Beta.contract 1 (lam 2 (app (var 1) (app successorTerm (var 2)))) (var 0)
      using 1 <;> try rfl
  have h₂ : Beta (app (lam 2 (app (var 0) (app successorTerm (var 2)))) (numeral n))
      (app (var 0) (app successorTerm (numeral n))) := by
    convert Beta.contract 2 (app (var 0) (app successorTerm (var 2))) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ successorTerm_closed]
  exact ((beta_steps_oracle (.tail (.single (.app_left _ h₁)) h₂)).trans
    (oracle_steps_app_right _ (beta_steps_oracle (successorTerm_apply n)))).tail (.query (n + 1))

def tagProgram (tag : ℕ) : AlphaTerm := lam 1 (lam 2
  (app (app (app zeroTestTerm (var 2)) (numeral tag)) (app (var 1) (app predecessorTerm (var 2)))))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
@[simp] theorem tagProgram_closed (tag : ℕ) : (tagProgram tag).Closed := by
  unfold Closed tagProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [zeroTestTerm_closed, numeral_closed, predecessorTerm_closed]
  decide

theorem tagProgram_start (tag n : ℕ) :
    Relation.ReflTransGen Beta (app (app (tagProgram tag) (var 0)) (numeral n))
      (app (app (app zeroTestTerm (numeral n)) (numeral tag))
        (app (var 0) (app predecessorTerm (numeral n)))) := by
  have h₁ : Beta (app (tagProgram tag) (var 0))
      (lam 2 (app (app (app zeroTestTerm (var 2)) (numeral tag))
        (app (var 0) (app predecessorTerm (var 2))))) := by
    convert Beta.contract 1 (lam 2 (app (app (app zeroTestTerm (var 2)) (numeral tag))
      (app (var 1) (app predecessorTerm (var 2))))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed tag), subst_closed _ _ _ predecessorTerm_closed]
  have h₂ : Beta (app (lam 2 (app (app (app zeroTestTerm (var 2)) (numeral tag))
      (app (var 0) (app predecessorTerm (var 2))))) (numeral n))
      (app (app (app zeroTestTerm (numeral n)) (numeral tag))
        (app (var 0) (app predecessorTerm (numeral n)))) := by
    convert Beta.contract 2 (app (app (app zeroTestTerm (var 2)) (numeral tag))
      (app (var 0) (app predecessorTerm (var 2)))) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed tag), subst_closed _ _ _ predecessorTerm_closed]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    For the tail term, two beta steps expose $o(\LambdaSucc\,\ChurchNumeral{n})$. Successor reduces the query argument to $\ChurchNumeral{n+1}$, and one query returns $\ChurchNumeral{p(n+1)}$. For prefixing, two beta steps expose the zero test of the output coordinate. At coordinate zero it selects $\ChurchNumeral{t}$ without evaluating the query branch. At coordinate $n+1$ it selects $o(\LambdaPred\,\ChurchNumeral{n+1})$; predecessor returns $\ChurchNumeral{n}$, and one query gives $\ChurchNumeral{p(n)}$. These calculations cover coordinate zero and every successor coordinate. Both terms are closed, and confluence excludes other numeral outputs.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Prefixing and removing a tag
-/
theorem tagProgram_runs (p : ℕ → ℕ) (tag n : ℕ) :
    OracleRuns p (tagProgram tag) n (typeTwoTagName tag p n) := by
  apply (beta_steps_oracle (tagProgram_start tag n)).trans
  cases n with
  | zero => exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ n =>
    apply (beta_steps_oracle (branch_succ n _ _)).trans
    have hp : Relation.ReflTransGen Beta (app predecessorTerm (numeral (n + 1))) (numeral n) := by
      simpa using predecessorTerm_apply (n + 1)
    exact (oracle_steps_app_right _ (beta_steps_oracle hp)).tail (.query n)

/-- Query only the tag before selecting one of the two branch applications. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For closed programs $P,Q$, define a tag selector by
    $$\LambdaTagBranch{P}{Q}:=\lambdaab{a}{\lambdaab{b}{
    \LambdaZeroTest\,(a\ChurchNumeral{0})\,(Pab)\,(Qab)}}.$$
    Use the composition term $C_{P,Q}$ from §{sec:lambda-input-composition} to form
    $$\LambdaCoproductCase{P}{Q}:=
    \LambdaTagBranch{C_{P,\LambdaNameTail}}{C_{Q,\LambdaNameTail}}.$$
    All component programs are inserted as closed lambda terms. Both constructions are therefore closed and finite.
-/
def tagBranchProgram (P Q : AlphaTerm) : AlphaTerm := lam 1 (lam 2
  (app (app (app zeroTestTerm (app (var 1) (numeral 0))) (app (app P (var 1)) (var 2)))
    (app (app Q (var 1)) (var 2))))

theorem tagBranchProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (tagBranchProgram P Q).Closed := by
  unfold Closed tagBranchProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [zeroTestTerm_closed, numeral_closed, hP, hQ]
  decide

theorem tagBranchProgram_start {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (tagBranchProgram P Q) (var 0)) (numeral n))
      (app (app (app zeroTestTerm (app (var 0) (numeral 0)))
        (app (app P (var 0)) (numeral n))) (app (app Q (var 0)) (numeral n))) := by
  have h₁ : Beta (app (tagBranchProgram P Q) (var 0))
      (lam 2 (app (app (app zeroTestTerm (app (var 0) (numeral 0)))
        (app (app P (var 0)) (var 2))) (app (app Q (var 0)) (var 2)))) := by
    convert Beta.contract 1 (lam 2 (app (app (app zeroTestTerm (app (var 1) (numeral 0)))
      (app (app P (var 1)) (var 2))) (app (app Q (var 1)) (var 2)))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ hP, subst_closed _ _ _ hQ]
  have h₂ : Beta (app (lam 2 (app (app (app zeroTestTerm (app (var 0) (numeral 0)))
      (app (app P (var 0)) (var 2))) (app (app Q (var 0)) (var 2)))) (numeral n))
      (app (app (app zeroTestTerm (app (var 0) (numeral 0)))
        (app (app P (var 0)) (numeral n))) (app (app Q (var 0)) (numeral n))) := by
    convert Beta.contract 2 (app (app (app zeroTestTerm (app (var 0) (numeral 0)))
      (app (app P (var 0)) (var 2))) (app (app Q (var 0)) (var 2))) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ zeroTestTerm_closed,
      subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ hP, subst_closed _ _ _ hQ]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    First apply the tag selector to $o,\ChurchNumeral{n}$. Two beta steps expose the two branch applications and the test $o\ChurchNumeral{0}$. One query returns the tag. If the tag is zero, the zero-test and true-selection reductions return $P\,o\,\ChurchNumeral{n}$; if it is one, false selection returns $Q\,o\,\ChurchNumeral{n}$. These finite reductions do not reduce the discarded branch. Closedness of the branch programs ensures that the binder substitutions do not capture the input variable.
-/
theorem tagBranchProgram_zero {p : ℕ → ℕ} {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    (n : ℕ) (ht : p 0 = 0) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (tagBranchProgram P Q) (var 0)) (numeral n)) (app (app P (var 0)) (numeral n)) := by
  apply (beta_steps_oracle (tagBranchProgram_start hP hQ n)).trans
  have h : OracleStep p (app (var 0) (numeral 0)) (numeral 0) := by simpa only [ht] using OracleStep.query (p := p) 0
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm (.single h)) _) _).trans
  apply beta_steps_oracle (branch_zero _ _ ?_)
  rw [fv_app, fv_app, hP, numeral_closed, fv_var]
  simp

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    First apply the tag selector to $o,\ChurchNumeral{n}$. Two beta steps expose the two branch applications and the test $o\ChurchNumeral{0}$. One query returns the tag. If the tag is zero, the zero-test and true-selection reductions return $P\,o\,\ChurchNumeral{n}$; if it is one, false selection returns $Q\,o\,\ChurchNumeral{n}$. These finite reductions do not reduce the discarded branch. Closedness of the branch programs ensures that the binder substitutions do not capture the input variable.
-/
theorem tagBranchProgram_one {p : ℕ → ℕ} {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    (n : ℕ) (ht : p 0 = 1) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (tagBranchProgram P Q) (var 0)) (numeral n)) (app (app Q (var 0)) (numeral n)) := by
  apply (beta_steps_oracle (tagBranchProgram_start hP hQ n)).trans
  have h : OracleStep p (app (var 0) (numeral 0)) (numeral 1) := by simpa only [ht] using OracleStep.query (p := p) 0
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm (.single h)) _) _).trans
  exact beta_steps_oracle (branch_succ 0 _ _)

/-- Both tail substitutions are finite terms; only the selected application is reduced. -/
def coproductCaseProgram (P Q : AlphaTerm) : AlphaTerm :=
  tagBranchProgram (compositionProgram P tailProgram) (compositionProgram Q tailProgram)

theorem coproductCaseProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (coproductCaseProgram P Q).Closed :=
  tagBranchProgram_closed (compositionProgram_closed hP tailProgram_closed)
    (compositionProgram_closed hQ tailProgram_closed)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Now use $C_{P,\LambdaNameTail}$ and $C_{Q,\LambdaNameTail}$ as the two branch programs. The tail lemma supplies every digit of $\NameTail{p}$. The input-substitution proof of composition therefore transforms a finite reduction of the selected original program on that tail into a finite reduction with input name $p$. Concatenate this with the selector reduction. Only the selected program needs a successful computation. Confluence makes the resulting numeral output unique.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Tag-directed computation
-/
theorem coproductCaseProgram_zero {p : ℕ → ℕ} {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    {n m : ℕ} (ht : p 0 = 0) (h : OracleRuns (typeTwoTailName p) P n m) :
    OracleRuns p (coproductCaseProgram P Q) n m :=
  (tagBranchProgram_zero (compositionProgram_closed hP tailProgram_closed)
    (compositionProgram_closed hQ tailProgram_closed) n ht).trans
    (compositionProgram_runs hP tailProgram_closed h (tailProgram_runs p))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Now use $C_{P,\LambdaNameTail}$ and $C_{Q,\LambdaNameTail}$ as the two branch programs. The tail lemma supplies every digit of $\NameTail{p}$. The input-substitution proof of composition therefore transforms a finite reduction of the selected original program on that tail into a finite reduction with input name $p$. Concatenate this with the selector reduction. Only the selected program needs a successful computation. Confluence makes the resulting numeral output unique.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Tag-directed computation
-/
theorem coproductCaseProgram_one {p : ℕ → ℕ} {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    {n m : ℕ} (ht : p 0 = 1) (h : OracleRuns (typeTwoTailName p) Q n m) :
    OracleRuns p (coproductCaseProgram P Q) n m :=
  (tagBranchProgram_one (compositionProgram_closed hP tailProgram_closed)
    (compositionProgram_closed hQ tailProgram_closed) n ht).trans
    (compositionProgram_runs hQ tailProgram_closed h (tailProgram_runs p))

end NamedLambda.AlphaTerm

theorem tailProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes tailProgram (fun p : D => typeTwoTailName p.val) :=
  typeTwoComputes_iff_runs.mpr ⟨tailProgram_closed, fun p n => tailProgram_runs p.val n⟩

theorem tagProgram_computes (tag : ℕ) (D : Set (ℕ → ℕ)) :
    TypeTwoComputes (tagProgram tag) (fun p : D => typeTwoTagName tag p.val) :=
  typeTwoComputes_iff_runs.mpr ⟨tagProgram_closed tag, fun p n => tagProgram_runs p.val tag n⟩

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The prefixing terms $\LambdaNamePrefix{0}$ and $\LambdaNamePrefix{1}$ send every valid component name to a valid coproduct name of its image under the corresponding injection. The prefix lemma proves their computability. Composing a realizer of $h$ with these terms proves the forward implication.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Coproduct criterion
-/
theorem hasComputableRealizer_inl (δX : Representation X) (δY : Representation Y) :
    HasComputableRealizer δX (typeTwoCoproductRepresentation δX δY) Sum.inl := by
  let F : δX.domain → (typeTwoCoproductRepresentation δX δY).domain := fun p =>
    ⟨typeTwoTagName 0 p.val, Or.inl ⟨rfl, p.property⟩⟩
  refine ⟨F, ⟨tagProgram 0, tagProgram_computes 0 δX.domain⟩, ?_⟩
  intro p
  simp [F, typeTwoCoproductRepresentation, coproductNameValue, typeTwoTagName]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The prefixing terms $\LambdaNamePrefix{0}$ and $\LambdaNamePrefix{1}$ send every valid component name to a valid coproduct name of its image under the corresponding injection. The prefix lemma proves their computability. Composing a realizer of $h$ with these terms proves the forward implication.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Coproduct criterion
-/
theorem hasComputableRealizer_inr (δX : Representation X) (δY : Representation Y) :
    HasComputableRealizer δY (typeTwoCoproductRepresentation δX δY) Sum.inr := by
  let F : δY.domain → (typeTwoCoproductRepresentation δX δY).domain := fun p =>
    ⟨typeTwoTagName 1 p.val, Or.inr ⟨rfl, p.property⟩⟩
  refine ⟨F, ⟨tagProgram 1, tagProgram_computes 1 δY.domain⟩, ?_⟩
  intro p
  simp [F, typeTwoCoproductRepresentation, coproductNameValue, typeTwoTagName]

/-- Only the selected component name must lie in its realizer's domain. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let $P,Q$ compute name realizers of the two restricted maps. On a valid coproduct name $p$, the tag is zero or one, and $\NameTail{p}$ is valid for the selected summand. Its realizer therefore returns a valid output name. The tag-directed computation lemma shows that the single closed term $\LambdaCoproductCase{P}{Q}$ computes that output name coordinate by coordinate. Its represented value is $h$ of the input point. There is no requirement that the other realizer work on the same tail, or that membership in either name domain be decidable.
-/
theorem HasComputableRealizer.copair {δX : Representation X} {δY : Representation Y}
    {δZ : Representation Z} {f : X → Z} {g : Y → Z}
    (hf : HasComputableRealizer δX δZ f) (hg : HasComputableRealizer δY δZ g) :
    HasComputableRealizer (typeTwoCoproductRepresentation δX δY) δZ (Sum.elim f g) := by
  obtain ⟨F, ⟨P, hp⟩, hF⟩ := hf
  obtain ⟨G, ⟨Q, hq⟩, hG⟩ := hg
  obtain ⟨hc, hr⟩ := typeTwoComputes_iff_runs.mp hp
  obtain ⟨hd, hs⟩ := typeTwoComputes_iff_runs.mp hq
  let H : (typeTwoCoproductRepresentation δX δY).domain → δZ.domain := fun p =>
    if hp : p.val 0 = 0 then F ⟨typeTwoTailName p.val, coproductName_left δX δY p hp⟩
    else G ⟨typeTwoTailName p.val, (coproductName_right δX δY p hp).2⟩
  refine ⟨H, ⟨coproductCaseProgram P Q, ?_⟩, ?_⟩
  · rw [typeTwoComputes_iff_runs]
    refine ⟨coproductCaseProgram_closed hc hd, ?_⟩
    intro p n
    by_cases ht : p.val 0 = 0
    · have h := coproductCaseProgram_zero hc hd ht
        (hr ⟨typeTwoTailName p.val, coproductName_left δX δY p ht⟩ n)
      simpa only [H, dite_eq_left ht] using h
    · have h := coproductCaseProgram_one hc hd (coproductName_right δX δY p ht).1
        (hs ⟨typeTwoTailName p.val, (coproductName_right δX δY p ht).2⟩ n)
      simpa only [H, dite_eq_right ht] using h
  · intro p
    by_cases ht : p.val 0 = 0
    · simpa [H, typeTwoCoproductRepresentation, coproductNameValue, ht] using
        hF ⟨typeTwoTailName p.val, coproductName_left δX δY p ht⟩
    · simpa [H, typeTwoCoproductRepresentation, coproductNameValue, ht] using
        hG ⟨typeTwoTailName p.val, (coproductName_right δX δY p ht).2⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Coproduct criterion
-/
theorem hasComputableRealizer_coproduct_iff (δX : Representation X) (δY : Representation Y)
    (δZ : Representation Z) (h : X ⊕ Y → Z) :
    HasComputableRealizer (typeTwoCoproductRepresentation δX δY) δZ h ↔
      HasComputableRealizer δX δZ (h ∘ Sum.inl) ∧
      HasComputableRealizer δY δZ (h ∘ Sum.inr) := by
  constructor
  · intro hh
    exact ⟨hh.comp (hasComputableRealizer_inl δX δY), hh.comp (hasComputableRealizer_inr δX δY)⟩
  · rintro ⟨hf, hg⟩
    have he : Sum.elim (h ∘ Sum.inl) (h ∘ Sum.inr) = h := by
      funext x; cases x <;> rfl
    simpa only [he] using hf.copair hg

end PolishSpaceBook
