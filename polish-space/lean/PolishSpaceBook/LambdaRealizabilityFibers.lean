module

public import PolishSpaceBook.LambdaRealizerLogic
public import PolishSpaceBook.HeytingPreorderQuotient
public import Mathlib.Order.Category.HeytAlg

@[expose] public section

/-! # Heyting algebras of realizability predicates modulo mutual reducibility -/
namespace PolishSpaceBook.LambdaIndexPCA

open CategoryTheory Opposite

/-- A type wrapper keeps uniform reducibility separate from pointwise subset inclusion. -/
structure IndexedPredicate (I : Type*) where
  val : RealizabilityPredicate ℕ I

instance indexedPredicatePreorder (I : Type*) : Preorder (IndexedPredicate I) where
  le φ ψ := Reduces φ.val ψ.val
  lt φ ψ := Reduces φ.val ψ.val ∧ ¬Reduces ψ.val φ.val
  le_refl φ := reduces_refl φ.val
  le_trans _ _ _ := reduces_trans

abbrev RealizabilityFiber (I : Type*) := Antisymmetrization (IndexedPredicate I) (· ≤ ·)

def predicateClass {I : Type*} (φ : RealizabilityPredicate ℕ I) : RealizabilityFiber I :=
  toAntisymmetrization (· ≤ ·) ⟨φ⟩

@[simp] theorem predicateClass_le_iff {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    predicateClass φ ≤ predicateClass ψ ↔ Reduces φ ψ := Iff.rfl

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First form the quotient in each fiber explicitly. Write $\varphi\equiv\psi$ when $\varphi\le\psi$ and
    $\psi\le\varphi$. Reflexivity and transitivity make this an equivalence relation. If $\varphi\equiv\varphi'$ and
    $\psi\equiv\psi'$, transitivity gives $\varphi\le\psi$ if and only if $\varphi'\le\psi'$. Thus reducibility defines
    an order on equivalence classes, and this order is antisymmetric by the definition of $\equiv$.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Let $\mathcal P_{K_1}(I)$ be this preorder, quotiented by mutual reducibility if one wants literal posets. For a
    function $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    Thus
    $$\mathcal P_{K_1}:\opcat{\SetCat}\to\HeytAlgCat$$
    is contravariant on the base sets.
-/
@[simp] theorem predicateClass_eq_iff {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    predicateClass φ = predicateClass ψ ↔ Reduces φ ψ ∧ Reduces ψ φ :=
  ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

theorem and_reduces_mono {I : Type*} {φ φ' ψ ψ' : RealizabilityPredicate ℕ I}
    (hφ : Reduces φ φ') (hψ : Reduces ψ ψ') :
    Reduces (realizabilityAnd φ ψ) (realizabilityAnd φ' ψ') :=
  reduces_and_intro (reduces_trans (reduces_and_left φ ψ) hφ)
    (reduces_trans (reduces_and_right φ ψ) hψ)

theorem or_reduces_mono {I : Type*} {φ φ' ψ ψ' : RealizabilityPredicate ℕ I}
    (hφ : Reduces φ φ') (hψ : Reduces ψ ψ') :
    Reduces (realizabilityOr φ ψ) (realizabilityOr φ' ψ') :=
  or_reduces (reduces_trans hφ (reduces_or_left φ' ψ'))
    (reduces_trans hψ (reduces_or_right φ' ψ'))

theorem imp_reduces_mono {I : Type*} {φ φ' ψ ψ' : RealizabilityPredicate ℕ I}
    (hφ : Reduces φ' φ) (hψ : Reduces ψ ψ') :
    Reduces (realizabilityImp φ ψ) (realizabilityImp φ' ψ') := by
  apply (reduces_imp_iff _ _ _).mp
  exact reduces_trans
    (and_reduces_mono (reduces_refl _) hφ)
    (reduces_trans ((reduces_imp_iff _ φ ψ).mpr (reduces_refl _)) hψ)

instance indexedPredicateHeytingOps (I : Type*) : HeytingPreorderOps (IndexedPredicate I) where
  meet φ ψ := ⟨realizabilityAnd φ.val ψ.val⟩
  join φ ψ := ⟨realizabilityOr φ.val ψ.val⟩
  imp φ ψ := ⟨realizabilityImp φ.val ψ.val⟩
  top := ⟨realizabilityTop I⟩
  bot := ⟨realizabilityBot I⟩
  le_meet a b c := reduces_and_iff a.val b.val c.val
  join_le a b c := or_reduces_iff a.val b.val c.val
  imp_adj a b c := reduces_imp_iff a.val b.val c.val
  le_top a := reduces_top a.val
  bot_le a := bot_reduces a.val

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The propositional universal properties give the variance rules
    $$
    \begin{aligned}
    \varphi\le\varphi',\ \psi\le\psi'
    &\Longrightarrow\varphi\land\psi\le\varphi'\land\psi',\\
    \varphi\le\varphi',\ \psi\le\psi'
    &\Longrightarrow\varphi\lor\psi\le\varphi'\lor\psi',\\
    \varphi'\le\varphi,\ \psi\le\psi'
    &\Longrightarrow(\varphi\to\psi)\le(\varphi'\to\psi').
    \end{aligned}
    $$
    For the last implication, the assumptions give
    $$(\varphi\to\psi)\land\varphi'\le(\varphi\to\psi)\land\varphi\le\psi\le\psi',$$
    and the implication adjunction applies. Applying these rules in both directions shows that all operations are
    independent of the representatives. The meet, join, top, and bottom universal properties therefore hold on classes,
    as does the implication adjunction. This makes the quotient a Heyting algebra.
-/
instance realizabilityFiberHeyting (I : Type*) : HeytingAlgebra (RealizabilityFiber I) :=
  HeytingPreorderOps.quotientHeyting

@[simp] theorem predicateClass_and {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    predicateClass (realizabilityAnd φ ψ) = predicateClass φ ⊓ predicateClass ψ := rfl

@[simp] theorem predicateClass_or {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    predicateClass (realizabilityOr φ ψ) = predicateClass φ ⊔ predicateClass ψ := rfl

@[simp] theorem predicateClass_imp {I : Type*} (φ ψ : RealizabilityPredicate ℕ I) :
    predicateClass (realizabilityImp φ ψ) = predicateClass φ ⇨ predicateClass ψ := rfl

@[simp] theorem predicateClass_top (I : Type*) : predicateClass (realizabilityTop I) = ⊤ := rfl
@[simp] theorem predicateClass_bot (I : Type*) : predicateClass (realizabilityBot I) = ⊥ := rfl

/-- Reindexing descends to the quotient and preserves the full Heyting structure. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Let $\mathcal P_{K_1}(I)$ be this preorder, quotiented by mutual reducibility if one wants literal posets. For a
    function $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    Thus
    $$\mathcal P_{K_1}:\opcat{\SetCat}\to\HeytAlgCat$$
    is contravariant on the base sets.
-/
def fiberReindex {I J : Type*} (f : I → J) : HeytingHom (RealizabilityFiber J) (RealizabilityFiber I) where
  toFun := Quotient.map (fun φ => ⟨realizabilityReindex f φ.val⟩)
    (fun _ _ h => ⟨reindex_reduces f h.1, reindex_reduces f h.2⟩)
  map_inf' a b := Quotient.inductionOn₂ a b fun _ _ => rfl
  map_sup' a b := Quotient.inductionOn₂ a b fun _ _ => rfl
  map_bot' := rfl
  map_himp' a b := Quotient.inductionOn₂ a b fun _ _ => rfl

@[simp] theorem fiberReindex_class {I J : Type*} (f : I → J) (φ : RealizabilityPredicate ℕ J) :
    fiberReindex f (predicateClass φ) = predicateClass (realizabilityReindex f φ) := rfl

@[simp] theorem fiberReindex_id {I : Type*} (a : RealizabilityFiber I) :
    fiberReindex id a = a := Quotient.inductionOn a fun _ => rfl

@[simp] theorem fiberReindex_comp {I J K : Type*} (f : I → J) (g : J → K) (a : RealizabilityFiber K) :
    fiberReindex f (fiberReindex g a) = fiberReindex (g ∘ f) a :=
  Quotient.inductionOn a fun _ => rfl

/-- The actual contravariant functor into mathlib's category of Heyting algebras. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Reindexing preserves reducibility by keeping the same tracker. It therefore descends to classes. Its defining
    formula commutes pointwise with $\land,\lor,\to,\top,\bot$, so the induced map is a Heyting homomorphism. Moreover,
    $$\mathrm{id}^{\ast}=\mathrm{id},\qquad (g\circ f)^{\ast}=f^{\ast}\circ g^{\ast}.$$
    Both identities already hold on predicates. Hence the quotient fibers and reindexing maps form the required
    contravariant functor to $\HeytAlgCat$.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Let $\mathcal P_{K_1}(I)$ be this preorder, quotiented by mutual reducibility if one wants literal posets. For a
    function $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    Thus
    $$\mathcal P_{K_1}:\opcat{\SetCat}\to\HeytAlgCat$$
    is contravariant on the base sets.
-/
def realizabilityIndexedHeyting : (Type u)ᵒᵖ ⥤ HeytAlg.{u} where
  obj I := HeytAlg.of (RealizabilityFiber I.unop)
  map f := HeytAlg.ofHom (fiberReindex f.unop)
  map_id I := by
    apply HeytAlg.ext
    intro a
    exact fiberReindex_id a
  map_comp f g := by
    apply HeytAlg.ext
    intro a
    exact (fiberReindex_comp g.unop f.unop a).symm

end PolishSpaceBook.LambdaIndexPCA
