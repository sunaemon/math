module

public import PolishSpaceBook.SetTheoryModelAxioms
public import Mathlib.SetTheory.ZFC.Class

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Bounded-formula absoluteness

The syntax is mathlib's membership-language syntax. The complexity predicates
recognize bounded formulas and finite existential/universal prenex prefixes.
The proof works for classes as well as sets and only needs membership closure
of the smaller domain. It assumes no ZFC axioms in either domain.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

abbrev ClassDomain (C : ZFClass.{u}) := {x : ZFSet.{u} // C x}

instance (C : ZFClass.{u}) : membershipLanguage.Structure (ClassDomain C) where
  RelMap | .mem => fun xs => (xs 0).val ∈ (xs 1).val

def inclusion {M N : ZFClass.{u}} (hMN : M ⊆ N) (x : ClassDomain M) : ClassDomain N :=
  ⟨x.val, hMN x.property⟩

def variableIndex {n : ℕ} : membershipLanguage.Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => nomatch e
  | .var (.inr i) => i
  | .func f _ => nomatch f

lemma term_realize_class (C : ZFClass.{u}) {n : ℕ} (t : membershipLanguage.Term (Empty ⊕ Fin n))
    (v : Empty → ClassDomain C) (xs : Fin n → ClassDomain C) :
    t.realize (Sum.elim v xs) = xs (variableIndex t) := by
  cases t with
  | var a => cases a with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts => exact f.elim

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    In the Lévy hierarchy, the quantifier is bounded only when the bounding object is already one of the available variables
    or terms whose atomic uses have been eliminated by bounded unfolding in the sense of §{sec:definitional-extensions}.
    This is why extension by definition and Lévy-complexity bookkeeping are kept separate.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Bounded quantifiers are the abbreviations introduced in §{sec:definitional-extensions} for languages containing $\in$.
-/
def boundedAll {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) i.castSucc).imp φ).all

def boundedExists {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula n :=
  (boundedAll i φ.not).not

@[simp] lemma realize_memberAt_class (C : ZFClass.{u}) {n : ℕ} (i j : Fin n)
    (v : Empty → ClassDomain C) (xs : Fin n → ClassDomain C) :
    (memberAt i j).Realize v xs ↔ (xs i).val ∈ (xs j).val := Iff.rfl

lemma realize_boundedAll (C : ZFClass.{u}) {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → ClassDomain C) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : ClassDomain C, y.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs y) := by
  simp only [boundedAll, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt_class, Fin.snoc_last, Fin.snoc_castSucc]

lemma realize_boundedExists (C : ZFClass.{u}) {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → ClassDomain C) :
    (boundedExists i φ).Realize Empty.elim xs ↔
      ∃ y : ClassDomain C, y.val ∈ (xs i).val ∧ φ.Realize Empty.elim (Fin.snoc xs y) := by
  classical
  simp only [boundedExists, BoundedFormula.realize_not, realize_boundedAll, not_forall,
    not_not, exists_prop]

/-- Syntactic bounded formulas, including Boolean combinations and bounded universal quantifiers. -/
inductive IsDeltaZero : {n : ℕ} → ForcingFormulas.Formula n → Prop
  | falsum {n} : IsDeltaZero (.falsum : ForcingFormulas.Formula n)
  | equal {n} (s t : membershipLanguage.Term (Empty ⊕ Fin n)) : IsDeltaZero (.equal s t)
  | member {n} (ts : Fin 2 → membershipLanguage.Term (Empty ⊕ Fin n)) : IsDeltaZero (.rel .mem ts)
  | imp {n} {φ ψ : ForcingFormulas.Formula n} : IsDeltaZero φ → IsDeltaZero ψ → IsDeltaZero (φ.imp ψ)
  | all {n} (i : Fin n) {φ : ForcingFormulas.Formula (n + 1)} : IsDeltaZero φ → IsDeltaZero (boundedAll i φ)

lemma IsDeltaZero.not {n} {φ : ForcingFormulas.Formula n} (h : IsDeltaZero φ) : IsDeltaZero φ.not :=
  .imp h .falsum

lemma IsDeltaZero.and {n} {φ ψ : ForcingFormulas.Formula n} (hφ : IsDeltaZero φ) (hψ : IsDeltaZero ψ) :
    IsDeltaZero (φ ⊓ ψ) := (hφ.imp hψ.not).not

lemma IsDeltaZero.or {n} {φ ψ : ForcingFormulas.Formula n} (hφ : IsDeltaZero φ) (hψ : IsDeltaZero ψ) :
    IsDeltaZero (φ ⊔ ψ) := hφ.not.imp hψ

lemma IsDeltaZero.exists {n} (i : Fin n) {φ : ForcingFormulas.Formula (n + 1)} (h : IsDeltaZero φ) :
    IsDeltaZero (boundedExists i φ) := (IsDeltaZero.all i h.not).not

/-- Bounded witnesses in the larger domain already belong to the smaller transitive domain. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] We first prove the $\Delta_0$ statement in the form used below. Let $M\IncludedIn N$ be transitive
    models or transitive classes, and let the parameters $\vec p$ lie in $M$. We show by induction on $\Delta_0$ formulas
    $\delta(\vec x)$ that
    $$
    M\models \delta(\vec p)
    \quad\Longleftrightarrow\quad
    N\models \delta(\vec p).
    $$
    After the bounded unfolding convention above, we may work in the pure language $L_\in$, so the only terms are variables.
    The atomic cases are $u=v$ and $u\in v$. Since $M$ is a subclass of $N$ and both structures use the actual equality and
    membership relations restricted to their elements, these atomic formulas have the same truth value for assignments from
    $M$. Boolean connectives are immediate from the induction hypothesis.

    It remains to check bounded quantifiers. Suppose $\delta(\vec p)$ has the form $\exists x\in a\,\psi(x,\vec p)$, where
    $a\in M$. In $M$ this means that some $b\in M$ satisfies $b\in a$ and $M\models\psi(b,\vec p)$. Because $M$ is
    transitive, every element of $a$ already lies in $M$. Hence the possible witnesses in $M$ are exactly the actual
    elements of $a$:
    $$
    M\models \exists x\in a\,\psi(x,\vec p)
    \quad\Longleftrightarrow\quad
    \text{for some } b\in a,\; M\models\psi(b,\vec p).
    $$
    The same set $a$ belongs to $N$, and its elements are the same actual elements $b\in a$. For each such $b$, the
    induction hypothesis gives
    $$
    M\models\psi(b,\vec p)
    \quad\Longleftrightarrow\quad
    N\models\psi(b,\vec p).
    $$
    Therefore
    $$
    M\models \exists x\in a\,\psi(x,\vec p)
    \quad\Longleftrightarrow\quad
    N\models \exists x\in a\,\psi(x,\vec p).
    $$
    The bounded universal case is the same argument with "for every" in place of "for some":
    $$
    M\models \forall x\in a\,\psi(x,\vec p)
    \quad\Longleftrightarrow\quad
    \text{for every } b\in a,\; M\models\psi(b,\vec p).
    $$
    Applying the induction hypothesis for each $b\in a$ gives
    $$
    \text{for every } b\in a,\; M\models\psi(b,\vec p)
    \quad\Longleftrightarrow\quad
    \text{for every } b\in a,\; N\models\psi(b,\vec p).
    $$
    Since $a$ has the same elements in $N$, this is equivalent to
    $$
    N\models \forall x\in a\,\psi(x,\vec p).
    $$
-/
theorem delta_zero_absolute (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} {φ : ForcingFormulas.Formula n}
    (hφ : IsDeltaZero φ) (xs : Fin n → ClassDomain M) :
    φ.Realize Empty.elim xs ↔ φ.Realize Empty.elim (inclusion hMN ∘ xs) := by
  induction hφ with
  | falsum => rfl
  | equal s t =>
    simp only [BoundedFormula.Realize, term_realize_class, Subtype.ext_iff]
    rfl
  | member ts =>
    simp only [BoundedFormula.Realize, term_realize_class]
    rfl
  | imp hφ hψ ihφ ihψ =>
    simp only [BoundedFormula.Realize, ihφ xs, ihψ xs]
  | all i hφ ih =>
    rw [realize_boundedAll, realize_boundedAll]
    constructor
    · intro h y hy
      let z : ClassDomain M := ⟨y.val, hM (xs i).val (xs i).property y.val hy⟩
      have hz : inclusion hMN z = y := Subtype.ext rfl
      have ht := (ih (Fin.snoc xs z)).mp (h z hy)
      rw [Fin.comp_snoc, hz] at ht
      exact ht
    · intro h y hy
      apply (ih (Fin.snoc xs y)).mpr
      rw [Fin.comp_snoc]
      exact h (inclusion hMN y) hy

/-- Finite existential prefixes of bounded formulas. -/
inductive IsSigmaOne : {n : ℕ} → ForcingFormulas.Formula n → Prop
  | delta {n} {φ : ForcingFormulas.Formula n} : IsDeltaZero φ → IsSigmaOne φ
  | ex {n} {φ : ForcingFormulas.Formula (n + 1)} : IsSigmaOne φ → IsSigmaOne φ.ex

/-- Finite universal prefixes of bounded formulas. -/
inductive IsPiOne : {n : ℕ} → ForcingFormulas.Formula n → Prop
  | delta {n} {φ : ForcingFormulas.Formula n} : IsDeltaZero φ → IsPiOne φ
  | all {n} {φ : ForcingFormulas.Formula (n + 1)} : IsPiOne φ → IsPiOne φ.all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Now let $\varphi(\vec p)$ be $\Sigma_1$, say
    $$
    \varphi(\vec p)\equiv \exists x_1\cdots\exists x_n\,\delta(x_1,\ldots,x_n,\vec p),
    $$
    with $\delta$ $\Delta_0$. If $M\models\varphi(\vec p)$, choose witnesses $a_1,\ldots,a_n\in M$. By $\Delta_0$
    absoluteness,\termref{absoluteness}
    $$
    N\models\delta(a_1,\ldots,a_n,\vec p),
    $$
    so $N\models\varphi(\vec p)$. Thus $\Sigma_1$ formulas are upward absolute.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For formulas in the displayed syntactic forms, this proof uses only transitivity of $M$ and the actual
    membership and equality relations on $M\IncludedIn N$; it needs no ZFC axioms in either domain.
-/
theorem sigma_one_upward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} {φ : ForcingFormulas.Formula n}
    (hφ : IsSigmaOne φ) (xs : Fin n → ClassDomain M) :
    φ.Realize Empty.elim xs → φ.Realize Empty.elim (inclusion hMN ∘ xs) := by
  induction hφ with
  | delta h => exact (delta_zero_absolute M N hMN hM h xs).mp
  | ex h ih =>
    rw [BoundedFormula.realize_ex, BoundedFormula.realize_ex]
    rintro ⟨y, hy⟩
    refine ⟨inclusion hMN y, ?_⟩
    have ht := ih (Fin.snoc xs y) hy
    rw [Fin.comp_snoc] at ht
    exact ht

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Finally let $\theta(\vec p)$ be $\Pi_1$, say
    $$
    \theta(\vec p)\equiv \forall x_1\cdots\forall x_n\,\delta(x_1,\ldots,x_n,\vec p),
    $$
    with $\delta$ $\Delta_0$. Suppose $N\models\theta(\vec p)$. To show $M\models\theta(\vec p)$, take arbitrary
    $a_1,\ldots,a_n\in M$. Since $M\IncludedIn N$, these are also elements of $N$, so
    $$
    N\models\delta(a_1,\ldots,a_n,\vec p).
    $$
    By $\Delta_0$ absoluteness, $M\models\delta(a_1,\ldots,a_n,\vec p)$. The tuple from $M$ was arbitrary, hence
    $M\models\theta(\vec p)$. Thus $\Pi_1$ formulas are downward absolute.
-/
theorem pi_one_downward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} {φ : ForcingFormulas.Formula n}
    (hφ : IsPiOne φ) (xs : Fin n → ClassDomain M) :
    φ.Realize Empty.elim (inclusion hMN ∘ xs) → φ.Realize Empty.elim xs := by
  induction hφ with
  | delta h => exact (delta_zero_absolute M N hMN hM h xs).mpr
  | all h ih =>
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    intro ht y
    apply ih (Fin.snoc xs y)
    rw [Fin.comp_snoc]
    exact ht (inclusion hMN y)

/-- Extensionality also holds for a transitive class with actual membership. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $N$ be transitive. If $x,y\in N$ have the same members in $N$, all their actual members lie in $N$,
    so they have the same members externally. External Extensionality gives $x=y$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Extensionality and Foundation in a transitive domain
-/
theorem class_models_extensionality (C : ZFClass.{u})
    (hC : ∀ a, C a → ∀ b ∈ a, C b) : ClassDomain C ⊨ extensionalitySentence := by
  classical
  have heq {n : ℕ} (i j : Fin n) (v : Empty → ClassDomain C)
      (xs : Fin n → ClassDomain C) : (equalAt i j).Realize v xs ↔ xs i = xs j := Iff.rfl
  simp only [extensionalitySentence, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
    realize_memberAt_class, heq, Fin.snoc]
  intro x y h
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (h ⟨z, hC x.val x.property z hz⟩).mp hz
  · intro hz
    exact (h ⟨z, hC y.val y.property z hz⟩).mpr hz

/-- The ambient Foundation axiom supplies a member of the transitive class. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For Foundation, let $x\in N$ have a member in $N$. It is externally nonempty, so external Foundation gives
    $y\in x$ with $x\cap y=\emptyset$. Transitivity gives $y\in N$.
    There is no $z\in N$ belonging to both $x$ and $y$, so this $y$ also witnesses the internal Foundation axiom.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Extensionality and Foundation in a transitive domain
-/
theorem class_models_foundation (C : ZFClass.{u})
    (hC : ∀ a, C a → ∀ b ∈ a, C b) : ClassDomain C ⊨ foundationSentence := by
  classical
  simp only [foundationSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, realize_memberAt_class, Fin.snoc]
  intro x hx
  obtain ⟨z, hz⟩ := hx
  change z.val ∈ x.val at hz
  have hne : x.val ≠ ∅ := by
    intro he
    rw [he] at hz
    exact ZFSet.notMem_empty _ hz
  obtain ⟨y, hy, hxy⟩ := ZFSet.regularity x.val hne
  refine ⟨⟨y, hC x.val x.property y hy⟩, hy, ?_⟩
  intro w hwy hwx
  have h : w.val ∈ x.val ∩ y := ZFSet.mem_inter.mpr ⟨hwx, hwy⟩
  rw [hxy] at h
  exact ZFSet.notMem_empty _ h

end PolishSpaceBook.SetTheoryModels
