module

public import PolishSpaceBook.ForcingGenericTruth
public import PolishSpaceBook.SetTheoryPredicateReflection
public import Mathlib.Order.BooleanAlgebra.Basic

@[expose] public section

/-! # Internally complete Boolean algebras and values of forcing formulas

Completeness below applies only to subsets coded in the ground model. The
external carrier is not assumed to be a complete Boolean algebra. Formula
values are constructed from the already proved atomic and formula recursion.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

/-- A carrier element with no inherited subset order: Boolean order is supplied
by the algebra, not by the ambient set-theoretic inclusion relation. -/
@[ext] structure BooleanElement (B : ZFSet.{u}) where
  val : ZFSet.{u}
  property : val ∈ B

/-- An internal Boolean algebra with represented finite operations and internal
completeness. The supremum axiom ranges over actual members of the model. -/
structure InternalBooleanAlgebra {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)] where
  orderCode : M
  complementCode : M
  meetCode : M
  order_iff : ∀ a b : BooleanElement B.val, pair a.val b.val ∈ orderCode.val ↔ a ≤ b
  complement_iff : ∀ a b : BooleanElement B.val, pair a.val b.val ∈ complementCode.val ↔ b = aᶜ
  meet_iff : ∀ a b c : BooleanElement B.val,
    pair (pair a.val b.val) c.val ∈ meetCode.val ↔ c = a ⊓ b
  complete : ∀ S : M, S.val ⊆ B.val → ∃ b : BooleanElement B.val,
    IsLUB {a : BooleanElement B.val | a.val ∈ S.val} b

namespace InternalBooleanAlgebra
variable {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)]

/-- The actual positive carrier; its internal membership follows by Separation. -/
def positiveSet : ZFSet.{u} := B.val.sep (· ≠ (⊥ : BooleanElement B.val).val)

lemma mem_positiveSet (x : ZFSet.{u}) :
    x ∈ positiveSet B ↔ x ∈ B.val ∧ x ≠ (⊥ : BooleanElement B.val).val := mem_sep

def element (p : Condition (positiveSet B)) : BooleanElement B.val :=
  ⟨p.val, ((mem_positiveSet B p.val).mp p.property).1⟩

lemma element_ne_bot (p : Condition (positiveSet B)) : element B p ≠ ⊥ := by
  intro he
  exact ((mem_positiveSet B p.val).mp p.property).2 (congrArg BooleanElement.val he)

def positive (b : BooleanElement B.val) (hb : b ≠ ⊥) : Condition (positiveSet B) :=
  ⟨b.val, (mem_positiveSet B b.val).mpr ⟨b.property,
    fun he => hb (BooleanElement.ext he)⟩⟩

@[simp] lemma element_positive (b : BooleanElement B.val) (hb : b ≠ ⊥) :
    element B (positive B b hb) = b := rfl

@[simp] lemma positive_element (p : Condition (positiveSet B)) :
    positive B (element B p) (element_ne_bot B p) = p := by cases p; rfl

instance positivePreorder : Preorder (Condition (positiveSet B)) :=
  Preorder.lift (element B)

lemma positive_le_iff (p q : Condition (positiveSet B)) :
    p ≤ q ↔ element B p ≤ element B q := Iff.rfl

lemma positiveSet_mem (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    positiveSet B ∈ M := by
  let z : M := ⟨(⊥ : BooleanElement B.val).val, hM.mem_trans (⊥ : BooleanElement B.val).property B.property⟩
  exact (BoundedSetPredicate.neg (.equal 1 0)).separation_mem hM (hsep _) ![z] B.property

variable (A : InternalBooleanAlgebra B)

lemma positive_order_iff (p q : Condition (positiveSet B)) :
    pair p.val q.val ∈ A.orderCode.val ↔ p ≤ q :=
  A.order_iff (element B p) (element B q)

def internalSup (S : M) (hS : S.val ⊆ B.val) : BooleanElement B.val := (A.complete S hS).choose

lemma internalSup_isLUB (S : M) (hS : S.val ⊆ B.val) :
    IsLUB {a : BooleanElement B.val | a.val ∈ S.val} (A.internalSup B S hS) :=
  (A.complete S hS).choose_spec

/-- A lower, density-saturated positive set is the principal ideal of any
supremum of its elements. No completeness assumption enters this lemma. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Conversely, suppose $p\le b_\varphi$ but $p\notin S_\varphi$. Saturation gives a nonzero $q\le p$
    such that no nonzero extension of $q$ belongs to $S_\varphi$. For every $s\in S_\varphi$, downward
    closure then gives $q\land s=0$, so $s\le\neg q$. The supremum property gives
    $b_\varphi\le\neg q$, contradicting $0<q\le p\le b_\varphi$. This proves the forcing inequality.
-/
theorem principal_ideal (S : Set (Condition (positiveSet B)))
    (hl : IsLowerSet S) (hs : forcingDense S ⊆ S) (b : BooleanElement B.val)
    (hb : IsLUB (element B '' S) b) (p : Condition (positiveSet B)) :
    p ∈ S ↔ element B p ≤ b := by
  constructor
  · intro hp
    exact hb.1 ⟨p, hp, rfl⟩
  · intro hp
    apply hs
    intro q hqp
    have hq : element B q ≤ b := (show element B q ≤ element B p from hqp).trans hp
    have hex : ∃ s ∈ S, element B q ⊓ element B s ≠ ⊥ := by
      by_contra hn
      have hu : ∀ s ∈ S, element B s ≤ (element B q)ᶜ := by
        intro s hs
        apply le_compl_iff_disjoint_left.mpr
        apply disjoint_iff.mpr
        by_contra hd
        exact hn ⟨s, hs, hd⟩
      have hbq : b ≤ (element B q)ᶜ := hb.2 (by
        rintro a ⟨s, hs, rfl⟩
        exact hu s hs)
      exact element_ne_bot B q ((le_compl_self).mp (hq.trans hbq))
    obtain ⟨s, hs, hmeet⟩ := hex
    let r := positive B (element B q ⊓ element B s) hmeet
    exact ⟨r, inf_le_left, hl (show r ≤ s from inf_le_right) hs⟩

/-- Positive principal ideals determine their Boolean element, including zero. -/
theorem eq_of_positive_le_iff (a b : BooleanElement B.val)
    (h : ∀ p : Condition (positiveSet B), element B p ≤ a ↔ element B p ≤ b) : a = b := by
  apply le_antisymm
  · by_cases ha : a = ⊥
    · rw [ha]; exact bot_le
    · exact (h (positive B a ha)).mp le_rfl
  · by_cases hb : b = ⊥
    · rw [hb]; exact bot_le
    · exact (h (positive B b hb)).mpr le_rfl

section Model
variable (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

abbrev positiveInModel : M := ⟨positiveSet B, positiveSet_mem B hM hsep⟩

include A hM hinf hpair hunion hpower hsep hrep in
lemma booleanForcingSet_mem {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : forcingSet (positiveSet B) M φ xs ∈ M :=
  forcingSet_mem hM hinf hpair hunion hpower hsep hrep
    (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) φ xs

lemma booleanForcingSet_subset {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : forcingSet (positiveSet B) M φ xs ⊆ B.val := by
  intro x hx
  exact ((mem_positiveSet B x).mp (mem_sep.mp hx).1).1

/-- A genuine Boolean element obtained by internal completeness from the
internally definable set produced by the atomic/formula forcing recursion. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}[Construction of the Boolean values]
    For the set-theoretic application, fix a transitive ground model $M$ of ZFC and a Boolean algebra
    $\mathbb B\in M$ that is complete as computed in $M$. Completeness is required only for subsets
    belonging to $M$. Given a formula $\varphi$ and its name parameters in $M$, forcing definability and
    Separation give
    $$S_\varphi:=\{p\in\mathbb B^+:p\forces^*\varphi\}\in M.$$
    Define its Boolean value $b_\varphi$ to be the supremum of $S_\varphi$ computed in $M$.
-/
def booleanValue {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : BooleanElement B.val :=
  A.internalSup B ⟨forcingSet (positiveSet B) M φ xs,
    booleanForcingSet_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩
    (booleanForcingSet_subset B φ xs)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For set-theoretic formulas, use the recursively defined relation $p\forces^*\varphi$ from
    §{sec:forcing-relation}. A condition $p\in\mathbb B^+$ satisfies this relation exactly when
    $$p\le[\![\varphi]\!].$$
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    The set $S_\varphi$ is downward closed and saturated under forcing density by §{sec:forcing-relation}.
    Thus $p\in S_\varphi$ implies $p\le b_\varphi$.
-/
theorem force_iff_le_booleanValue {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) (p : Condition (positiveSet B)) :
    p ∈ force (positiveSet B) M φ xs ↔
      element B p ≤ booleanValue B A hM hinf hpair hunion hpower hsep hrep φ xs := by
  apply principal_ideal B _ (force_lower _ _ φ xs) (force_saturated _ _ φ xs)
  have he : element B '' force (positiveSet B) M φ xs =
      {a : BooleanElement B.val | a.val ∈ forcingSet (positiveSet B) M φ xs} := by
    ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (mem_forcingSet _ _ φ xs p).mpr hp
    · intro ha
      have hp : a.val ∈ positiveSet B := (mem_sep.mp ha).1
      exact ⟨⟨a.val, hp⟩, (mem_forcingSet _ _ φ xs ⟨a.val, hp⟩).mp ha, rfl⟩
  rw [he]
  exact A.internalSup_isLUB B ⟨_, booleanForcingSet_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩
    (booleanForcingSet_subset B φ xs)

end Model

/-- The Boolean filter lifted from positive conditions. -/
def liftedFilter (G : Order.PFilter (Condition (positiveSet B))) : Set (BooleanElement B.val) :=
  {b | ∃ hb : b ≠ ⊥, positive B b hb ∈ G}

lemma mem_liftedFilter_iff (G : Order.PFilter (Condition (positiveSet B))) (b : BooleanElement B.val) :
    b ∈ liftedFilter B G ↔ ∃ p ∈ G, element B p ≤ b := by
  constructor
  · rintro ⟨hb, hG⟩
    exact ⟨positive B b hb, hG, le_rfl⟩
  · rintro ⟨p, hpG, hpb⟩
    have hb : b ≠ ⊥ := fun he => element_ne_bot B p (le_antisymm (he ▸ hpb) bot_le)
    exact ⟨hb, G.mem_of_le (show p ≤ positive B b hb from hpb) hpG⟩

/-- Truth in the actual evaluated-name extension equals membership of the
constructed Boolean value in the lifted generic filter. Countability is absent. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The forcing extension appears when one evaluates this structured truth through a generic filter. Let $\mathbb
    B$ be the complete Boolean algebra as computed in the ground model $M$.
    If $G\IncludedIn\mathbb B$ is $M$-generic, then
    $$
    M[G]\models\varphi
    \quad\Longleftrightarrow\quad
    [\![\varphi]\!]\in G,
    $$
    for formulas interpreted by names in the \termuse{Boolean-valued model}. The filter evaluates the truth values
    of formulas whose names lie in $M$.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Indeed, the truth lemma in §{sec:forcing-relation} says that $\varphi$ holds in $M[G]$ exactly when
    some $p\in G$ satisfies $p\forces^*\varphi$. The Boolean inequality and upward closure of $G$ make this equivalent to
    membership of the Boolean value in $G$. Conversely, a Boolean value belonging to the proper filter
    $G$ is itself a nonzero condition and forces the formula. No countability assumption on $M$ is needed
    once the generic filter is given.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    After evaluating at an $M$-generic filter $G$, the Boolean-valued semantics collapses to the ordinary two-valued truth
    of $M[G]$. Thus forcing changes the universe while retaining classical first-order logic.
-/
theorem boolean_generic_truth
    (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (G : Order.PFilter (Condition (positiveSet B))) (hG : ModelGeneric (positiveSet B) M G)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name (positiveSet B) M) :
    φ.Realize Empty.elim (fun i => evalName (positiveSet B) M G (xs i)) ↔
      booleanValue B A hM hinf hpair hunion hpower hsep hrep φ xs ∈ liftedFilter B G := by
  rw [mem_liftedFilter_iff]
  simp_rw [← force_iff_le_booleanValue B A hM hinf hpair hunion hpower hsep hrep]
  exact (modelGeneric_truth hM hinf hpair hunion hpower hsep hrep
    (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) G hG φ xs).symm

end InternalBooleanAlgebra
end PolishSpaceBook.SetTheoryModels
