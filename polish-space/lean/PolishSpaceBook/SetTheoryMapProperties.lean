module

public import PolishSpaceBook.SetTheoryPredicateReflection
public import PolishSpaceBook.SetTheoryLevyHierarchy

@[expose] public section

/-! # Bounded tests for injective, surjective and bijective set graphs

The shared bounded-predicate compiler handles syntax, boundedness and internal
interpretation. Only the descriptions of the three mathematical tests are new.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- The extra test in the book's injectivity clause, with a,b,c as the last
three bound variables. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$
    \begin{aligned}
    \mathrm{Inj}_{x,y}(f)
    &:\equiv\; f : x \to y \;\land{}\\
    &\qquad \forall a \in x\, \forall b \in x\, \forall c \in y\,
    (f(a)=c \land f(b)=c \to a=b),\\
    \mathrm{Surj}_{x,y}(f)
    &:\equiv\; f : x \to y \;\land\; \forall c \in y\, \exists a \in x\,(f(a)=c),\\
    \mathrm{Bij}_{x,y}(f)
    &:\equiv\; \mathrm{Inj}_{x,y}(f) \;\land\; \mathrm{Surj}_{x,y}(f).
    \end{aligned}
    $$
-/
def injectiveGraphPredicate {n : ℕ} (x y f : Fin n) : BoundedSetPredicate n :=
  .conj (.function x y f)
    (.all x (.all x.castSucc (.all y.castSucc.castSucc
      (.disj (.neg (.conj
        (.pairMember f.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc (Fin.last (n + 2)))
        (.pairMember f.castSucc.castSucc.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)))))
        (.equal (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc)))))

def surjectiveGraphPredicate {n : ℕ} (x y f : Fin n) : BoundedSetPredicate n :=
  .conj (.function x y f)
    (.all y (.ex x.castSucc
      (.pairMember f.castSucc.castSucc (Fin.last (n + 1)) (Fin.last n).castSucc)))

def bijectiveGraphPredicate {n : ℕ} (x y f : Fin n) : BoundedSetPredicate n :=
  .conj (injectiveGraphPredicate x y f) (surjectiveGraphPredicate x y f)

def injectiveGraphFormula {n : ℕ} (x y f : Fin n) : ForcingFormulas.Formula n :=
  (injectiveGraphPredicate x y f).compile

def surjectiveGraphFormula {n : ℕ} (x y f : Fin n) : ForcingFormulas.Formula n :=
  (surjectiveGraphPredicate x y f).compile

def bijectiveGraphFormula {n : ℕ} (x y f : Fin n) : ForcingFormulas.Formula n :=
  (bijectiveGraphPredicate x y f).compile

theorem injectiveGraphFormula_deltaZero {n : ℕ} (x y f : Fin n) :
    IsDeltaZero (injectiveGraphFormula x y f) := (injectiveGraphPredicate x y f).compile_deltaZero

theorem surjectiveGraphFormula_deltaZero {n : ℕ} (x y f : Fin n) :
    IsDeltaZero (surjectiveGraphFormula x y f) := (surjectiveGraphPredicate x y f).compile_deltaZero

theorem bijectiveGraphFormula_deltaZero {n : ℕ} (x y f : Fin n) :
    IsDeltaZero (bijectiveGraphFormula x y f) := (bijectiveGraphPredicate x y f).compile_deltaZero

/-- Unfolding the descriptions gives precisely the displayed graph conditions. -/
theorem realize_injectiveGraphFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → M) :
    (injectiveGraphFormula x y f).Realize Empty.elim xs ↔
      IsFunc (xs x).val (xs y).val (xs f).val ∧
      ∀ a ∈ (xs x).val, ∀ b ∈ (xs x).val, ∀ c ∈ (xs y).val,
        pair a c ∈ (xs f).val ∧ pair b c ∈ (xs f).val → a = b := by
  rw [injectiveGraphFormula, BoundedSetPredicate.realize_compile hM]
  simp only [injectiveGraphPredicate, BoundedSetPredicate.eval, Function.comp_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  simp only [← imp_iff_not_or]

theorem realize_surjectiveGraphFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → M) :
    (surjectiveGraphFormula x y f).Realize Empty.elim xs ↔
      IsFunc (xs x).val (xs y).val (xs f).val ∧
      ∀ c ∈ (xs y).val, ∃ a ∈ (xs x).val, pair a c ∈ (xs f).val := by
  rw [surjectiveGraphFormula, BoundedSetPredicate.realize_compile hM]
  simp only [surjectiveGraphPredicate, BoundedSetPredicate.eval, Function.comp_apply,
    Fin.snoc_castSucc, Fin.snoc_last]

theorem realize_bijectiveGraphFormula {M : ZFSet.{u}} (_hM : M.IsTransitive)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → M) :
    (bijectiveGraphFormula x y f).Realize Empty.elim xs ↔
      (injectiveGraphFormula x y f).Realize Empty.elim xs ∧
      (surjectiveGraphFormula x y f).Realize Empty.elim xs :=
  BoundedFormula.realize_inf

/-- All three tests retain their truth between transitive domains. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    All quantifiers remain bounded by $f$, $x$, or $y$. Therefore $\mathrm{Inj}_{x,y}(f)$, $\mathrm{Surj}_{x,y}(f)$, and
    $\mathrm{Bij}_{x,y}(f)$ are $\Delta_0$, hence absolute between transitive models containing the parameters.
-/
theorem mapProperties_absolute (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} (x y f : Fin n)
    (xs : Fin n → ClassDomain M) :
    ((injectiveGraphFormula x y f).Realize Empty.elim xs ↔
      (injectiveGraphFormula x y f).Realize Empty.elim (inclusion hMN ∘ xs)) ∧
    ((surjectiveGraphFormula x y f).Realize Empty.elim xs ↔
      (surjectiveGraphFormula x y f).Realize Empty.elim (inclusion hMN ∘ xs)) ∧
    ((bijectiveGraphFormula x y f).Realize Empty.elim xs ↔
      (bijectiveGraphFormula x y f).Realize Empty.elim (inclusion hMN ∘ xs)) :=
  ⟨delta_zero_absolute M N hMN hM (injectiveGraphFormula_deltaZero x y f) xs,
    delta_zero_absolute M N hMN hM (surjectiveGraphFormula_deltaZero x y f) xs,
    delta_zero_absolute M N hMN hM (bijectiveGraphFormula_deltaZero x y f) xs⟩

/-- Omega is an explicit parameter, not an implicitly absolute constant. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Cardinals and countability.**
    $$
    \begin{aligned}
    \mathrm{Countable}(x)
    &:\equiv\; \exists f\,\mathrm{Inj}_{x,\omega}(f).
    \end{aligned}
    $$
-/
def countableSetFormula {n : ℕ} (x omega : Fin n) : ForcingFormulas.Formula n :=
  (injectiveGraphFormula x.castSucc omega.castSucc (Fin.last n)).ex

theorem countableSetFormula_sigmaOne {n : ℕ} (x omega : Fin n) :
    IsSigmaOne (countableSetFormula x omega) :=
  .ex (.delta (injectiveGraphFormula_deltaZero _ _ _))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here $\omega$ is supplied as a fixed parameter. The body is $\Delta_0$, so one outermost unbounded existential
    puts $\mathrm{Countable}$ at $\Sigma_1$. It is therefore
    upward absolute: if a transitive model already has an injection $x\to\omega$, any larger transitive model sees the same
    injection.
-/
theorem countableSetFormula_upward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} (x omega : Fin n)
    (xs : Fin n → ClassDomain M) :
    (countableSetFormula x omega).Realize Empty.elim xs →
      (countableSetFormula x omega).Realize Empty.elim (inclusion hMN ∘ xs) :=
  sigma_one_upward M N hMN hM (countableSetFormula_sigmaOne x omega) xs

/-- A canonical three-slot test can be used independently of the surrounding
parameter context. -/
theorem realize_bijectiveGraphFormula_slots {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → M) :
    (bijectiveGraphFormula x y f).Realize Empty.elim xs ↔
      (bijectiveGraphFormula (0 : Fin 3) 1 2).Realize Empty.elim ![xs x, xs y, xs f] := by
  simp only [realize_bijectiveGraphFormula hM, realize_injectiveGraphFormula hM,
    realize_surjectiveGraphFormula hM, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  rfl

/-- Put the unbounded graph variable first. The remaining ordinal and
smaller-ordinal tests are bounded, so this is a genuine Pi-one formula. -/
def cardinalSetFormula {n : ℕ} (kappa : Fin n) : ForcingFormulas.Formula n :=
  ((ordinalFormula kappa.castSucc) ⊓ boundedAll kappa.castSucc
    (bijectiveGraphFormula (Fin.last (n + 1)) kappa.castSucc.castSucc
      (Fin.last n).castSucc).not).all

theorem cardinalSetFormula_piOne {n : ℕ} (kappa : Fin n) :
    IsPiOne (cardinalSetFormula kappa) :=
  .all (.delta ((ordinalFormula_deltaZero _).and
    (.all _ (bijectiveGraphFormula_deltaZero _ _ _).not)))

theorem cardinalSetFormula_levyPi {n : ℕ} (kappa : Fin n) :
    LevyPi 1 (cardinalSetFormula kappa) :=
  LevyPi.of_prefix ((universalPrefix_delta_iff _).mpr (cardinalSetFormula_piOne kappa))

/-- Commuting the two universal quantifiers gives exactly the book's
"no smaller ordinal bijects with kappa" definition. No Collection is needed
for this particular bounded/unbounded universal interchange. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now define cardinalhood by saying that $\kappa$ is an ordinal and no smaller ordinal bijects with it:
    $$
    \mathrm{Card}(\kappa)
    \;:\equiv\;
    \mathrm{Ord}(\kappa)
    \land
    \forall \alpha \in \kappa\, \neg \exists f\,\mathrm{Bij}_{\alpha,\kappa}(f).
    $$
    The predicate $\mathrm{Bij}_{\alpha,\kappa}(f)$ is $\Delta_0$, so $\exists f\,\mathrm{Bij}_{\alpha,\kappa}(f)$ is
    $\Sigma_1$ and its negation is $\Pi_1$. Here the bounded universal quantifier can be moved past the universal
    quantifier over $f$, giving the equivalent form
    $$\forall f\,\bigl[\mathrm{Ord}(\kappa)\land
    \forall\alpha\in\kappa\,\neg\mathrm{Bij}_{\alpha,\kappa}(f)\bigr].$$
    Its matrix is $\Delta_0$, so $\mathrm{Card}(\kappa)$ is $\Pi_1$; this particular rearrangement needs no Collection.
-/
theorem realize_cardinalSetFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (kappa : Fin n) (xs : Fin n → M) :
    (cardinalSetFormula kappa).Realize Empty.elim xs ↔
      (xs kappa).val.IsOrdinal ∧
      ∀ a : M, a.val ∈ (xs kappa).val →
        ¬∃ f : M, (bijectiveGraphFormula (0 : Fin 3) 1 2).Realize Empty.elim ![a, xs kappa, f] := by
  simp only [cardinalSetFormula, BoundedFormula.realize_all, BoundedFormula.realize_inf,
    realize_ordinalFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha),
    realize_boundedAll, BoundedFormula.realize_not, Fin.snoc_castSucc]
  simp only [realize_bijectiveGraphFormula_slots hM (Fin.last (n + 1))
    kappa.castSucc.castSucc (Fin.last n).castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    refine ⟨(h (xs kappa)).1, ?_⟩
    intro a ha hf
    obtain ⟨f, hf⟩ := hf
    exact (h f).2 a ha hf
  · rintro ⟨hord, h⟩ f
    exact ⟨hord, fun a ha hf => h a ha ⟨f, hf⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Hence cardinalhood is downward
    absolute: a cardinal of $V$ remains a cardinal in any transitive submodel containing it.
-/
theorem cardinalSetFormula_downward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} (kappa : Fin n)
    (xs : Fin n → ClassDomain M) :
    (cardinalSetFormula kappa).Realize Empty.elim (inclusion hMN ∘ xs) →
      (cardinalSetFormula kappa).Realize Empty.elim xs :=
  pi_one_downward M N hMN hM (cardinalSetFormula_piOne kappa) xs

end PolishSpaceBook.SetTheoryModels
