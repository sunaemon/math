module

public import PolishSpaceBook.ForcingFormulas

@[expose] public section

/-!
# First-order set-theoretic axioms in arbitrary structures

These are sentences of the membership language already used for forcing.
Their satisfaction lemmas expose quantification over the model's elements;
external closure is proved separately, using transitivity.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

abbrev variableAt {n : ℕ} (i : Fin n) : membershipLanguage.Term (Empty ⊕ Fin n) := .var (.inr i)
def memberAt {n : ℕ} (i j : Fin n) : ForcingFormulas.Formula n := .rel .mem ![variableAt i, variableAt j]
def equalAt {n : ℕ} (i j : Fin n) : ForcingFormulas.Formula n := .equal (variableAt i) (variableAt j)

namespace AbstractMembership

/-- Membership as interpreted by an arbitrary structure for the membership language. -/
def member {S : Type u} [membershipLanguage.Structure S] (a b : S) : Prop :=
  Structure.RelMap (L := membershipLanguage) MembershipSymbol.mem ![a, b]

lemma realize_memberAt (S : Type u) [membershipLanguage.Structure S]
    {n : ℕ} (i j : Fin n) (v : Empty → S) (xs : Fin n → S) :
    (memberAt i j).Realize v xs ↔ member (xs i) (xs j) := by
  change Structure.RelMap (L := membershipLanguage) MembershipSymbol.mem _ ↔
    Structure.RelMap (L := membershipLanguage) MembershipSymbol.mem _
  apply Iff.of_eq
  congr 1
  funext k
  fin_cases k <;> rfl

lemma realize_equalAt (S : Type u) [membershipLanguage.Structure S]
    {n : ℕ} (i j : Fin n) (v : Empty → S) (xs : Fin n → S) :
    (equalAt i j).Realize v xs ↔ xs i = xs j := Iff.rfl

end AbstractMembership

@[simp] lemma realize_memberAt (S : ZFSet.{u}) {n : ℕ} (i j : Fin n) (v : Empty → S) (xs : Fin n → S) :
    (memberAt i j).Realize v xs ↔ (xs i).val ∈ (xs j).val := Iff.rfl

@[simp] lemma realize_equalAt (S : ZFSet.{u}) {n : ℕ} (i j : Fin n) (v : Empty → S) (xs : Fin n → S) :
    (equalAt i j).Realize v xs ↔ xs i = xs j := Iff.rfl

def emptySentence : membershipLanguage.Sentence := ((memberAt 1 0).not.all).ex

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Pairing.** For any sets $a, b$, the set $\{a, b\}$ exists: $\forall a\, \forall b\, \exists p\, \forall x\,(x \in
        p \leftrightarrow x = a \lor x = b)$.
-/
def pairingSentence : membershipLanguage.Sentence :=
  (((memberAt (3 : Fin 4) 2).iff (equalAt 3 0 ⊔ equalAt 3 1)).all.ex).all.all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Union.** For any set $x$, the set $\bigcup x$ exists: $\forall x\, \exists u\, \forall z\,(z \in u \leftrightarrow
        \exists y\,(z \in y \land y \in x))$.
-/
def unionSentence : membershipLanguage.Sentence :=
  (((memberAt (2 : Fin 3) 1).iff ((memberAt (2 : Fin 4) 3 ⊓ memberAt 3 0).ex)).all.ex).all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Power Set.** For any set $x$, the set $\PowerSet{x}$ of subsets of $x$ exists: $\forall x\, \exists p\, \forall
        z\,(z \in p \leftrightarrow z \IncludedIn x)$.
-/
def powerSentence : membershipLanguage.Sentence :=
  (((memberAt (2 : Fin 3) 1).iff ((memberAt (3 : Fin 4) 2).imp (memberAt 3 0)).all).all.ex).all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Extensionality.** Two sets are equal iff they have the same elements: $\forall x\, \forall y\, [\forall z\,(z \in
        x \leftrightarrow z \in y) \to x = y]$.
-/
def extensionalitySentence : membershipLanguage.Sentence :=
  ((((memberAt (2 : Fin 3) 0).iff (memberAt 2 1)).all).imp (equalAt 0 1)).all.all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Foundation.** Every nonempty set has an $\in$-minimal element: $\forall x\,(x \ne \emptyset \to \exists y \in
        x\,(y \cap x = \emptyset))$. Equivalently, $\in$ is well-founded on sets. In particular, no set contains
        itself; this consequence
        alone is weaker than Foundation.
-/
def foundationSentence : membershipLanguage.Sentence :=
  (((memberAt (1 : Fin 2) 0).ex).imp
    ((memberAt (1 : Fin 2) 0 ⊓ ((memberAt (2 : Fin 3) 1).imp (memberAt 2 0).not).all).ex)).all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Infinity.** An inductive set exists:
        $$\exists x\,\big[\exists e\,(e \in x \land \forall z\, z \notin e) \land \forall y \in x\, \exists s \in x\,
        \forall w\,(w \in s \leftrightarrow w \in y \lor w = y)\big].$$
        After the abbreviations below are introduced, this is:
        $$\exists x\,(\emptyset \in x \land \forall y \in x\,(y \cup \{y\} \in x)).$$
        The $\IncludedIn$-least such set is $\omega$.
-/
def infinitySentence : membershipLanguage.Sentence :=
  (((memberAt (1 : Fin 2) 0 ⊓ (memberAt (2 : Fin 3) 1).not.all).ex) ⊓
    (((memberAt (1 : Fin 2) 0).imp
      ((memberAt (2 : Fin 3) 0 ⊓
        ((memberAt (3 : Fin 4) 2).iff (memberAt 3 1 ⊔ equalAt 3 1)).all).ex)).all)).ex

namespace AbstractMembership

lemma models_empty_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ emptySentence ↔ ∃ e : S, ∀ z : S, ¬ member z e := by
  classical
  simp [emptySentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt]

end AbstractMembership

lemma models_empty_iff (S : ZFSet.{u}) : S ⊨ emptySentence ↔ ∃ e : S, ∀ z : S, z.val ∉ e.val :=
  AbstractMembership.models_empty_iff S

namespace AbstractMembership

lemma models_pairing_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ pairingSentence ↔
    ∀ a b : S, ∃ p : S, ∀ x : S, member x p ↔ x = a ∨ x = b := by
  classical
  simp [pairingSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt, realize_equalAt]

end AbstractMembership

lemma models_pairing_iff (S : ZFSet.{u}) : S ⊨ pairingSentence ↔
    ∀ a b : S, ∃ p : S, ∀ x : S, x.val ∈ p.val ↔ x = a ∨ x = b :=
  AbstractMembership.models_pairing_iff S

namespace AbstractMembership

lemma models_union_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ unionSentence ↔
    ∀ x : S, ∃ v : S, ∀ z : S, member z v ↔ ∃ y : S, member z y ∧ member y x := by
  classical
  simp [unionSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt]

end AbstractMembership

lemma models_union_iff (S : ZFSet.{u}) : S ⊨ unionSentence ↔
    ∀ x : S, ∃ v : S, ∀ z : S, z.val ∈ v.val ↔ ∃ y : S, z.val ∈ y.val ∧ y.val ∈ x.val :=
  AbstractMembership.models_union_iff S

namespace AbstractMembership

lemma models_power_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ powerSentence ↔
    ∀ x : S, ∃ p : S, ∀ z : S, member z p ↔ ∀ w : S, member w z → member w x := by
  classical
  simp [powerSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt]

end AbstractMembership

lemma models_power_iff (S : ZFSet.{u}) : S ⊨ powerSentence ↔
    ∀ x : S, ∃ p : S, ∀ z : S, z.val ∈ p.val ↔ ∀ w : S, w.val ∈ z.val → w.val ∈ x.val :=
  AbstractMembership.models_power_iff S

namespace AbstractMembership

lemma models_extensionality_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ extensionalitySentence ↔
    ∀ x y : S, (∀ z : S, member z x ↔ member z y) → x = y := by
  classical
  simp [extensionalitySentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt, realize_equalAt]

end AbstractMembership

lemma models_extensionality_iff (S : ZFSet.{u}) : S ⊨ extensionalitySentence ↔
    ∀ x y : S, (∀ z : S, z.val ∈ x.val ↔ z.val ∈ y.val) → x = y :=
  AbstractMembership.models_extensionality_iff S

namespace AbstractMembership

lemma models_foundation_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ foundationSentence ↔
    ∀ x : S, (∃ y : S, member y x) →
      ∃ y : S, member y x ∧ ∀ z : S, member z y → ¬ member z x := by
  classical
  simp [foundationSentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt]

end AbstractMembership

lemma models_foundation_iff (S : ZFSet.{u}) : S ⊨ foundationSentence ↔
    ∀ x : S, (∃ y : S, y.val ∈ x.val) →
      ∃ y : S, y.val ∈ x.val ∧ ∀ z : S, z.val ∈ y.val → z.val ∉ x.val :=
  AbstractMembership.models_foundation_iff S

namespace AbstractMembership

lemma models_infinity_iff (S : Type u) [membershipLanguage.Structure S] : S ⊨ infinitySentence ↔
    ∃ x : S, (∃ e : S, member e x ∧ ∀ z : S, ¬ member z e) ∧
      ∀ y : S, member y x → ∃ s : S, member s x ∧
        ∀ w : S, member w s ↔ member w y ∨ w = y := by
  classical
  simp [infinitySentence, Sentence.Realize, FirstOrder.Language.Formula.Realize, Fin.snoc, realize_memberAt, realize_equalAt]

end AbstractMembership

lemma models_infinity_iff (S : ZFSet.{u}) : S ⊨ infinitySentence ↔
    ∃ x : S, (∃ e : S, e.val ∈ x.val ∧ ∀ z : S, z.val ∉ e.val) ∧
      ∀ y : S, y.val ∈ x.val → ∃ s : S, s.val ∈ x.val ∧
        ∀ w : S, w.val ∈ s.val ↔ w.val ∈ y.val ∨ w = y :=
  AbstractMembership.models_infinity_iff S

namespace AbstractMembership

lemma models_empty_of_infinity {S : Type u} [membershipLanguage.Structure S] (h : S ⊨ infinitySentence) : S ⊨ emptySentence := by
  obtain ⟨_, ⟨e, _, he⟩, _⟩ := (models_infinity_iff S).mp h
  exact (models_empty_iff S).mpr ⟨e, he⟩

end AbstractMembership

lemma models_empty_of_infinity {S : ZFSet.{u}} (h : S ⊨ infinitySentence) : S ⊨ emptySentence :=
  AbstractMembership.models_empty_of_infinity h

namespace AbstractMembership

/-- Pairing and Foundation rule out self-membership in any membership structure. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Foundation.** Every nonempty set has an $\in$-minimal element: $\forall x\,(x \ne \emptyset \to \exists y \in
        x\,(y \cap x = \emptyset))$. Equivalently, $\in$ is well-founded on sets. In particular, no set contains
        itself; this consequence
        alone is weaker than Foundation.
-/
theorem not_member_self_of_foundation {S : Type u} [membershipLanguage.Structure S]
    (hp : S ⊨ pairingSentence) (hf : S ⊨ foundationSentence) (x : S) : ¬member x x := by
  intro hxx
  obtain ⟨p, hsing⟩ := (models_pairing_iff S).mp hp x x
  have hxp : member x p := (hsing x).mpr (Or.inl rfl)
  obtain ⟨y, hyp, hy⟩ := (models_foundation_iff S).mp hf p ⟨x, hxp⟩
  have hyx : y = x := (hsing y).mp hyp |>.elim id id
  subst y
  exact hy x hxx hxp

end AbstractMembership

end PolishSpaceBook.SetTheoryModels
