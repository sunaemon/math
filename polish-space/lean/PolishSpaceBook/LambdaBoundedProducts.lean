module

public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # Numerical primitive recursion and bounded products of tests -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def curryThird (F : AlphaTerm) := lam 42 (curryNumerical (app (curryNumerical F) (var 42)))

theorem curryThird_closed {F : AlphaTerm} (hF : F.Closed) : (curryThird F).Closed := by
  unfold curryThird curryNumerical Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hF,numericalPairTerm_closed]
  decide

theorem curryThird_apply {F : AlphaTerm} (hF : F.Closed) (x n r : ℕ) :
    Relation.ReflTransGen Beta (app (app (app (curryThird F) (numeral x)) (numeral n)) (numeral r))
      (app F (numeral (Nat.pair x (Nat.pair n r)))) := by
  have he : (curryNumerical (app (curryNumerical F) (var 42))).subst 42 (numeral x) =
      curryNumerical (app (curryNumerical F) (numeral x)) := by
    change (lam 40 (lam 41 (app (app (curryNumerical F) (var 42))
      (app (app numericalPairTerm (var 40)) (var 41))))).subst 42 (numeral x) = _
    rw [subst_lam_fresh _ _ 40 42 (by decide) (by rw [numeral_closed]; simp)]
    rw [subst_lam_fresh _ _ 41 42 (by decide) (by rw [numeral_closed]; simp)]
    simp only [subst_app,subst_var,subst_closed _ _ _ numericalPairTerm_closed]
    rw [subst_closed _ _ _ (curryNumerical_closed hF)]
    simp
    rfl
  have hs : Beta (app (curryThird F) (numeral x))
      (curryNumerical (app (curryNumerical F) (numeral x))) := by
    rw [← he]; exact Beta.contract 42 _ _
  apply (beta_steps_app_left (beta_steps_app_left (.single hs) _) _).trans
  exact (curryNumerical_apply (closed_app (curryNumerical_closed hF) (numeral_closed x)) n r).trans
    (curryNumerical_apply hF x (Nat.pair n r))

def numericalRecursion (B H : AlphaTerm) := uncurryNumerical (parameterRecursor B (curryThird H))

theorem numericalRecursion_computes {B H : AlphaTerm} {b h : ℕ → ℕ}
    (hb : NumericalComputes B b) (hh : NumericalComputes H h) :
    NumericalComputes (numericalRecursion B H)
      (fun z => primitiveRec (b z.unpair.1)
        (fun k r => h (Nat.pair z.unpair.1 (Nat.pair k r))) z.unpair.2) := by
  unfold numericalRecursion
  refine uncurryNumerical_computes (parameterRecursor_closed hb.1 (curryThird_closed hh.1))
    (fun x n => primitiveRec (b x) (fun k r => h (Nat.pair x (Nat.pair k r))) n) ?_
  intro x n
  exact parameterRecursor_apply hb.1 (curryThird_closed hh.1) (numeral_closed x) _ _ (hb.2 x)
    (fun k r => (curryThird_apply hh.1 x k r).trans (hh.2 _)) n

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Next let a closed term $T$ compute a total numerical test $t$ on paired inputs. Numerical projections, pairing and
    multiplication construct a closed handler $H_T$ with
    $$H_T\,\ChurchNumeral{x}\,\ChurchNumeral{n}\,\ChurchNumeral{r}
     \to_\beta^*\LambdaMul\,\ChurchNumeral{r}\,
     (T\,\ChurchNumeral{\NatPair{x}{n}}).$$
    More explicitly, first form the unary function on $\NatPair{x}{\NatPair{n}{r}}$ by these operations, and then curry it
    to three numerical arguments. With $B:=\lambdaab{x}{\ChurchNumeral{1}}$, put
    $$\LambdaBoundedProduct{T}:=\lambdaab{z}{
     \LambdaParamRec{B}{H_T}\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.$$
-/
def boundedProductStep (T : AlphaTerm) :=
  mulNumerical
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
    (numericalCompose T (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Next let a closed term $T$ compute a total numerical test $t$ on paired inputs. Numerical projections, pairing and
    multiplication construct a closed handler $H_T$ with
    $$H_T\,\ChurchNumeral{x}\,\ChurchNumeral{n}\,\ChurchNumeral{r}
     \to_\beta^*\LambdaMul\,\ChurchNumeral{r}\,
     (T\,\ChurchNumeral{\NatPair{x}{n}}).$$
    More explicitly, first form the unary function on $\NatPair{x}{\NatPair{n}{r}}$ by these operations, and then curry it
    to three numerical arguments. With $B:=\lambdaab{x}{\ChurchNumeral{1}}$, put
    $$\LambdaBoundedProduct{T}:=\lambdaab{z}{
     \LambdaParamRec{B}{H_T}\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.$$
-/
def boundedProductTerm (T : AlphaTerm) := numericalRecursion (numericalConstant 1) (boundedProductStep T)

def boundedProduct (t : ℕ → ℕ) (x : ℕ) : ℕ → ℕ :=
  primitiveRec 1 (fun k r => r * t (Nat.pair x k))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Bounded products of numerical tests
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Apply parameterized primitive recursion to $B,H_T$. Its reduction theorem gives the recurrence for $b_n$. Induction on
    $N$, using that a product of natural numbers is nonzero exactly when both factors are nonzero, gives the stated
    criterion. The same induction proves the zero-or-one assertion. The initial case is the empty product, so it imposes no
    tests.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Next let a closed term $T$ compute a total numerical test $t$ on paired inputs. Numerical projections, pairing and
    multiplication construct a closed handler $H_T$ with
    $$H_T\,\ChurchNumeral{x}\,\ChurchNumeral{n}\,\ChurchNumeral{r}
     \to_\beta^*\LambdaMul\,\ChurchNumeral{r}\,
     (T\,\ChurchNumeral{\NatPair{x}{n}}).$$
    More explicitly, first form the unary function on $\NatPair{x}{\NatPair{n}{r}}$ by these operations, and then curry it
    to three numerical arguments. With $B:=\lambdaab{x}{\ChurchNumeral{1}}$, put
    $$\LambdaBoundedProduct{T}:=\lambdaab{z}{
     \LambdaParamRec{B}{H_T}\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.$$
-/
theorem boundedProduct_computes {T : AlphaTerm} {t : ℕ → ℕ} (ht : NumericalComputes T t) :
    NumericalComputes (boundedProductTerm T) (fun z => boundedProduct t z.unpair.1 z.unpair.2) := by
  have hf := projection_computes true
  have hs := projection_computes false
  have hh := ((projection_computes false).comp hs).mul
    (ht.comp (hf.pair ((projection_computes true).comp hs)))
  simpa [boundedProductTerm,boundedProductStep,boundedProduct,Nat.unpair_pair] using
    numericalRecursion_computes (numericalConstant_computes 1) hh

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Bounded products of numerical tests
-/
theorem boundedProduct_ne_zero (t : ℕ → ℕ) (x N : ℕ) :
    boundedProduct t x N ≠ 0 ↔ ∀ n < N, t (Nat.pair x n) ≠ 0 := by
  induction N with
  | zero => simp [boundedProduct,primitiveRec]
  | succ N ih =>
    change boundedProduct t x N * t (Nat.pair x N) ≠ 0 ↔ _
    rw [mul_ne_zero_iff,ih]
    constructor
    · rintro ⟨h,hN⟩ n hn
      by_cases hlt : n < N
      · exact h n hlt
      · have : n = N := by omega
        simpa [this] using hN
    · intro h
      exact ⟨fun n hn => h n (by omega),h N (by omega)⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Bounded products of numerical tests
-/
theorem boundedProduct_zero_or_one (t : ℕ → ℕ) (x N : ℕ)
    (ht : ∀ n, t (Nat.pair x n) = 0 ∨ t (Nat.pair x n) = 1) :
    boundedProduct t x N = 0 ∨ boundedProduct t x N = 1 := by
  induction N with
  | zero => exact Or.inr rfl
  | succ N ih =>
    change boundedProduct t x N * t (Nat.pair x N) = 0 ∨
      boundedProduct t x N * t (Nat.pair x N) = 1
    rcases ih with h | h <;> rcases ht N with hn | hn <;> simp [h,hn]

end PolishSpaceBook.NamedLambda.AlphaTerm
