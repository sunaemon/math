module

public import PolishSpaceBook.SetTheoryRelationFormulas

@[expose] public section

/-! # Bounded formulas for set-coded functions -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- All members of the graph are pairs with the prescribed source and target. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    **Maps.** With application read as graph membership, the assertion that $f$ is a function from $x$ to $y$ is:
    $$
    \begin{aligned}
    f : x \to y \;:\equiv\;&
    (\forall p \in f\, \exists a \in x\, \exists b \in y\, p = \langle a,b\rangle)\\
    &{}\land
    \forall a \in x\, \exists b \in y\,
    \bigl(f(a)=b \land \forall c \in y\,(f(a)=c \to c=b)\bigr).
    \end{aligned}
    $$
    Every quantifier is bounded by $f$, $x$, or $y$, and the remaining pair/application notation unfolds with bounded
    quantifiers. Hence $f:x\to y$ is $\Delta_0$.
-/
def relationFormula {n : ℕ} (x y f : Fin n) : ForcingFormulas.Formula n :=
  boundedAll f (productFormula x.castSucc y.castSucc (Fin.last n))

/-- A selected value is the unique value in the prescribed target. -/
def uniqueValueFormula {n : ℕ} (y f a b : Fin n) : ForcingFormulas.Formula n :=
  pairMemberFormula f a b ⊓ boundedAll y
    ((pairMemberFormula f.castSucc a.castSucc (Fin.last n)).imp
      (equalAt (Fin.last n) b.castSucc))

/-- Totality and uniqueness, together with the bound on every graph member. -/
def functionFormula {n : ℕ} (x y f : Fin n) : ForcingFormulas.Formula n :=
  relationFormula x y f ⊓ boundedAll x (boundedExists y.castSucc
    (uniqueValueFormula y.castSucc.castSucc f.castSucc.castSucc
      (Fin.last n).castSucc (Fin.last (n + 1))))

lemma relationFormula_deltaZero {n : ℕ} (x y f : Fin n) : IsDeltaZero (relationFormula x y f) :=
  .all f (productFormula_deltaZero _ _ _)

lemma uniqueValueFormula_deltaZero {n : ℕ} (y f a b : Fin n) :
    IsDeltaZero (uniqueValueFormula y f a b) :=
  (pairMemberFormula_deltaZero _ _ _).and
    (.all y ((pairMemberFormula_deltaZero _ _ _).imp (equalAt_deltaZero _ _)))

lemma functionFormula_deltaZero {n : ℕ} (x y f : Fin n) : IsDeltaZero (functionFormula x y f) :=
  (relationFormula_deltaZero _ _ _).and (.all x (.exists y.castSucc (uniqueValueFormula_deltaZero _ _ _ _)))

lemma realize_relationFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → ClassDomain C) :
    (relationFormula x y f).Realize Empty.elim xs ↔
      (xs f).val ⊆ ZFSet.prod (xs x).val (xs y).val := by
  simp only [relationFormula, realize_boundedAll, realize_productFormula C hC,
    Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h p hp
    exact h ⟨p, hC _ (xs f).property _ hp⟩ hp
  · intro h p hp
    exact h hp

lemma realize_uniqueValueFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (y f a b : Fin n) (xs : Fin n → ClassDomain C) :
    (uniqueValueFormula y f a b).Realize Empty.elim xs ↔
      ZFSet.pair (xs a).val (xs b).val ∈ (xs f).val ∧
      ∀ c ∈ (xs y).val, ZFSet.pair (xs a).val c ∈ (xs f).val → c = (xs b).val := by
  simp only [uniqueValueFormula, BoundedFormula.realize_inf, realize_boundedAll,
    BoundedFormula.realize_imp, realize_pairMemberFormula C hC, realize_equalAt_class,
    Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro c hc hpair
    exact congrArg Subtype.val (h ⟨c, hC _ (xs y).property _ hc⟩ hc hpair)
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun c hc hpair => Subtype.ext (h c.val hc hpair)⟩

/-- The bounded formula recognizes mathlib's canonical set-function predicate. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    For a transitive domain containing $f,x,y$, the first clause says exactly that $f\IncludedIn x\times y$:
    each actual member of $f$ lies in the domain, and the bounded pair clause recognizes its actual coordinates.
    The second clause gives a value for each actual $a\in x$ and uniqueness among values in $y$.
    Any pair $\langle a,c\rangle\in f$ already has $c\in y$ by the first clause, so this bounded uniqueness
    is uniqueness among all actual possible values. Conversely, an actual function supplies the same bounded
    witnesses, all of which lie in the domain by transitivity. Thus the internal predicate and the actual
    set-function condition agree; no closure under all external functions is used.
-/
lemma realize_functionFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x y f : Fin n) (xs : Fin n → ClassDomain C) :
    (functionFormula x y f).Realize Empty.elim xs ↔
      ZFSet.IsFunc (xs x).val (xs y).val (xs f).val := by
  simp only [functionFormula, BoundedFormula.realize_inf, realize_relationFormula C hC,
    realize_boundedAll, realize_boundedExists, realize_uniqueValueFormula C hC,
    Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨hsub, htotal⟩
    refine ⟨hsub, ?_⟩
    intro a ha
    obtain ⟨b, hb, hpair, huniq⟩ := htotal ⟨a, hC _ (xs x).property _ ha⟩ ha
    refine ⟨b.val, hpair, ?_⟩
    intro c hc
    exact huniq c (ZFSet.pair_mem_prod.mp (hsub hc)).2 hc
  · rintro ⟨hsub, htotal⟩
    refine ⟨hsub, ?_⟩
    intro a ha
    obtain ⟨b, hpair, huniq⟩ := htotal a.val ha
    have hb := (ZFSet.pair_mem_prod.mp (hsub hpair)).2
    exact ⟨⟨b, hC _ (xs y).property _ hb⟩, hb, hpair, fun c _ hc => huniq c hc⟩

lemma external_functionFormula (x y f : ZFSet.{u}) :
    externalRealize (functionFormula (0 : Fin 3) 1 2) (Fin.snoc ![x, y] f) ↔ ZFSet.IsFunc x y f := by
  simpa [externalRealize, Fin.snoc] using
    realize_functionFormula (⊤ : ZFClass.{u}) (fun _ _ _ _ => trivial) (0 : Fin 3) 1 2
      (fun i => ⟨Fin.snoc (α := fun _ => ZFSet.{u}) ![x, y] f i, trivial⟩)

end PolishSpaceBook.SetTheoryModels
