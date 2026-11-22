module

public import PolishSpaceBook.SetTheorySeparation

@[expose] public section

/-! # Bounded formulas for singletons, unordered pairs, ordered pairs, and products -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma memberAt_deltaZero {n : ℕ} (a b : Fin n) : IsDeltaZero (memberAt a b) := .member _
lemma equalAt_deltaZero {n : ℕ} (a b : Fin n) : IsDeltaZero (equalAt a b) := .equal _ _

@[simp] lemma realize_equalAt_class (C : ZFClass.{u}) {n : ℕ} (a b : Fin n)
    (v : Empty → ClassDomain C) (xs : Fin n → ClassDomain C) :
    (equalAt a b).Realize v xs ↔ xs a = xs b := Iff.rfl

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Here are explicit bounded expansions for the equalities used in this clause:
    $$\begin{aligned}
    u=\{a\}
    &\Longleftrightarrow a\in u\land\forall z\in u\,(z=a),\\
    v=\{a,b\}
    &\Longleftrightarrow a\in v\land b\in v\land\forall z\in v\,(z=a\lor z=b),\\
    q=\langle a,b\rangle
    &\Longleftrightarrow\exists u\in q\,\exists v\in q\,\bigl(
     u=\{a\}\land v=\{a,b\}\\
    &\qquad{}\land q=\{u,v\}\bigr).
    \end{aligned}$$
    In the last line, use the first two lines to expand the three remaining set equalities.
    The witnesses $u,v$ are allowed to coincide when $a=b$.
-/
def singletonFormula {n : ℕ} (s a : Fin n) : ForcingFormulas.Formula n :=
  memberAt a s ⊓ boundedAll s (equalAt (Fin.last n) a.castSucc)

def unorderedPairFormula {n : ℕ} (p a b : Fin n) : ForcingFormulas.Formula n :=
  memberAt a p ⊓ memberAt b p ⊓
    boundedAll p (equalAt (Fin.last n) a.castSucc ⊔ equalAt (Fin.last n) b.castSucc)

def orderedPairFormula {n : ℕ} (q a b : Fin n) : ForcingFormulas.Formula n :=
  boundedExists q (boundedExists q.castSucc
    (singletonFormula (Fin.last n).castSucc a.castSucc.castSucc ⊓
      unorderedPairFormula (Fin.last (n + 1)) a.castSucc.castSucc b.castSucc.castSucc ⊓
      unorderedPairFormula q.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1))))

def productFormula {n : ℕ} (x y q : Fin n) : ForcingFormulas.Formula n :=
  boundedExists x (boundedExists y.castSucc
    (orderedPairFormula q.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1))))

lemma singletonFormula_deltaZero {n : ℕ} (s a : Fin n) : IsDeltaZero (singletonFormula s a) :=
  (memberAt_deltaZero a s).and (.all s (equalAt_deltaZero _ _))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    First, atomic uses of pair notation are expanded contextually. For example,
    $$
    c \in \{a,b\}
    \quad\text{means}\quad
    c=a \lor c=b,
-/
lemma unorderedPairFormula_deltaZero {n : ℕ} (p a b : Fin n) :
    IsDeltaZero (unorderedPairFormula p a b) :=
  ((memberAt_deltaZero a p).and (memberAt_deltaZero b p)).and
    (.all p ((equalAt_deltaZero _ _).or (equalAt_deltaZero _ _)))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Bounded unfolding convention.** The formulas below use ordinary set-theoretic notation, but their hierarchy
    classification is always made after bounded unfolding into $L_\in$. The following clauses instantiate the
    $\Delta_0$-safe and contextual conventions of §{sec:definitional-extensions}.
-/
lemma orderedPairFormula_deltaZero {n : ℕ} (q a b : Fin n) :
    IsDeltaZero (orderedPairFormula q a b) :=
  .exists q (.exists q.castSucc
    (((singletonFormula_deltaZero _ _).and (unorderedPairFormula_deltaZero _ _ _)).and
      (unorderedPairFormula_deltaZero _ _ _)))

lemma productFormula_deltaZero {n : ℕ} (x y q : Fin n) : IsDeltaZero (productFormula x y q) :=
  .exists x (.exists y.castSucc (orderedPairFormula_deltaZero _ _ _))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    The first two equivalences follow from Extensionality. For the last, an ordered pair has the displayed
    singleton and unordered pair as members. Conversely, those two members together with $q=\{u,v\}$ give
    $q=\{\{a\},\{a,b\}\}$. In a transitive domain, all elements inspected by these bounded clauses remain in the
    domain. Thus the clauses recognize the actual singleton, unordered pair, and ordered pair; their correctness
    requires no assumption that the domain contains every externally constructed set.
-/
lemma realize_singletonFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (s a : Fin n) (xs : Fin n → ClassDomain C) :
    (singletonFormula s a).Realize Empty.elim xs ↔ (xs s).val = ({(xs a).val} : ZFSet.{u}) := by
  simp only [singletonFormula, BoundedFormula.realize_inf, realize_memberAt_class,
    realize_boundedAll, realize_equalAt_class, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨ha, h⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_singleton]
    constructor
    · intro hz
      exact congrArg Subtype.val (h ⟨z, hC _ (xs s).property z hz⟩ hz)
    · rintro rfl
      exact ha
  · intro he
    constructor
    · rw [he]
      exact ZFSet.mem_singleton.mpr rfl
    · intro z hz
      apply Subtype.ext
      rw [he] at hz
      exact ZFSet.mem_singleton.mp hz

lemma realize_unorderedPairFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (p a b : Fin n) (xs : Fin n → ClassDomain C) :
    (unorderedPairFormula p a b).Realize Empty.elim xs ↔
      (xs p).val = ({(xs a).val, (xs b).val} : ZFSet.{u}) := by
  simp only [unorderedPairFormula, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    realize_memberAt_class, realize_boundedAll, realize_equalAt_class,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_pair]
    constructor
    · intro hz
      rcases h ⟨z, hC _ (xs p).property z hz⟩ hz with hza | hzb
      · exact Or.inl (congrArg Subtype.val hza)
      · exact Or.inr (congrArg Subtype.val hzb)
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
  · intro he
    constructor
    · rw [he]
      exact ⟨ZFSet.mem_pair.mpr (Or.inl rfl), ZFSet.mem_pair.mpr (Or.inr rfl)⟩
    · intro z hz
      rw [he, ZFSet.mem_pair] at hz
      exact hz.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h))

lemma realize_orderedPairFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (q a b : Fin n) (xs : Fin n → ClassDomain C) :
    (orderedPairFormula q a b).Realize Empty.elim xs ↔
      (xs q).val = ZFSet.pair (xs a).val (xs b).val := by
  simp only [orderedPairFormula, realize_boundedExists, BoundedFormula.realize_inf,
    realize_singletonFormula C hC, realize_unorderedPairFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨s, _, p, _, ⟨hs, hp⟩, hq⟩
    simpa only [hs, hp, ZFSet.pair] using hq
  · intro hq
    have hs : ({(xs a).val} : ZFSet.{u}) ∈ (xs q).val := by simp [hq, ZFSet.pair]
    have hp : ({(xs a).val, (xs b).val} : ZFSet.{u}) ∈ (xs q).val := by simp [hq, ZFSet.pair]
    exact ⟨⟨_, hC _ (xs q).property _ hs⟩, hs, ⟨_, hC _ (xs q).property _ hp⟩, hp,
      ⟨rfl, rfl⟩, hq⟩

lemma realize_productFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x y q : Fin n) (xs : Fin n → ClassDomain C) :
    (productFormula x y q).Realize Empty.elim xs ↔
      (xs q).val ∈ ZFSet.prod (xs x).val (xs y).val := by
  simp only [productFormula, realize_boundedExists, realize_orderedPairFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc, ZFSet.mem_prod]
  constructor
  · rintro ⟨a, ha, b, hb, hq⟩
    exact ⟨a.val, ha, b.val, hb, hq⟩
  · rintro ⟨a, ha, b, hb, hq⟩
    exact ⟨⟨a, hC _ (xs x).property a ha⟩, ha, ⟨b, hC _ (xs y).property b hb⟩, hb, hq⟩

lemma external_productFormula (x y z : ZFSet.{u}) :
    externalRealize (productFormula (0 : Fin 3) 1 2) (Fin.snoc ![x, y] z) ↔ z ∈ ZFSet.prod x y := by
  simpa [externalRealize, Fin.snoc] using
    realize_productFormula (⊤ : ZFClass.{u}) (fun _ _ _ _ => trivial) (0 : Fin 3) 1 2
      (fun i => ⟨Fin.snoc (α := fun _ => ZFSet.{u}) ![x, y] z i, trivial⟩)

end PolishSpaceBook.SetTheoryModels
