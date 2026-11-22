module

public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Renaming and graph access for reflected finite tests -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.BoundedSetPredicate
open FirstOrder Language ZFSet ForcingFormulas
universe u

def liftRenaming {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.snoc (fun i => (ρ i).castSucc) (Fin.last m)

lemma snoc_comp_liftRenaming {n m : ℕ} {α : Type*} (ρ : Fin n → Fin m) (xs : Fin m → α) (x : α) :
    Fin.snoc xs x ∘ liftRenaming ρ = Fin.snoc (xs ∘ ρ) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRenaming]

def rename : {n m : ℕ} → BoundedSetPredicate n → (Fin n → Fin m) → BoundedSetPredicate m
  | _, _, .equal i j, ρ => .equal (ρ i) (ρ j)
  | _, _, .member i j, ρ => .member (ρ i) (ρ j)
  | _, _, .orderedPair p i j, ρ => .orderedPair (ρ p) (ρ i) (ρ j)
  | _, _, .pairMember r i j, ρ => .pairMember (ρ r) (ρ i) (ρ j)
  | _, _, .function a b g, ρ => .function (ρ a) (ρ b) (ρ g)
  | _, _, .successor a b, ρ => .successor (ρ a) (ρ b)
  | _, _, .subset a b, ρ => .subset (ρ a) (ρ b)
  | _, _, .neg p, ρ => .neg (p.rename ρ)
  | _, _, .conj p q, ρ => .conj (p.rename ρ) (q.rename ρ)
  | _, _, .disj p q, ρ => .disj (p.rename ρ) (q.rename ρ)
  | _, _, .iff p q, ρ => .iff (p.rename ρ) (q.rename ρ)
  | _, _, .all a p, ρ => .all (ρ a) (p.rename (liftRenaming ρ))
  | _, _, .ex a p, ρ => .ex (ρ a) (p.rename (liftRenaming ρ))

@[simp] theorem eval_rename {n m : ℕ} (p : BoundedSetPredicate n) (ρ : Fin n → Fin m)
    (xs : Fin m → ZFSet.{u}) : (p.rename ρ).eval xs ↔ p.eval (xs ∘ ρ) := by
  induction p generalizing m with
  | equal | member | orderedPair | pairMember | function | successor | subset => rfl
  | neg p ih => exact not_congr (ih ρ xs)
  | conj p q ihp ihq => exact and_congr (ihp ρ xs) (ihq ρ xs)
  | disj p q ihp ihq => exact or_congr (ihp ρ xs) (ihq ρ xs)
  | iff p q ihp ihq => exact iff_congr (ihp ρ xs) (ihq ρ xs)
  | all a p ih => simp only [rename, eval, ih, snoc_comp_liftRenaming, Function.comp_apply]
  | ex a p ih => simp only [rename, eval, ih, snoc_comp_liftRenaming, Function.comp_apply]

def imply {n : ℕ} (p q : BoundedSetPredicate n) : BoundedSetPredicate n := .disj (.neg p) q

@[simp] lemma eval_imply {n : ℕ} (p q : BoundedSetPredicate n) (xs : Fin n → ZFSet.{u}) :
    (p.imply q).eval xs ↔ (p.eval xs → q.eval xs) := by
  classical
  simp only [imply, eval, imp_iff_not_or]

/-- A binary graph value, with every auxiliary pair bounded by the graph itself. -/
def binaryMember : BoundedSetPredicate 4 :=
  .ex 0 (.ex 4 (.ex 5 (.conj (.orderedPair 6 1 2) (.orderedPair 4 6 3))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    An atomic binary-graph condition also has a bounded expansion: to express
    $\langle\langle u,v\rangle,z\rangle\in G$, quantify over $p\in G$, $s\in p$, and $r\in s$, and require
    $r=\langle u,v\rangle$ and $p=\langle r,z\rangle$. The Kuratowski pair supplies these witnesses.
    Thus no unbounded quantifier is hidden in the auxiliary tuple notation.
-/
lemma eval_binaryMember (G a b c : ZFSet.{u}) :
    binaryMember.eval ![G, a, b, c] ↔ pair (pair a b) c ∈ G := by
  change (∃ p ∈ G, ∃ s ∈ p, ∃ r ∈ s, r = pair a b ∧ p = pair r c) ↔ _
  constructor
  · rintro ⟨p, hp, s, _, r, _, rfl, rfl⟩
    exact hp
  · intro h
    refine ⟨pair (pair a b) c, h, {pair a b}, ?_, pair a b, ?_, rfl, rfl⟩ <;> simp [ZFSet.pair]

/-- Specify a subset of an ambient set by a bounded membership condition. -/
def setComprehension {n : ℕ} (ambient output : Fin n) (p : BoundedSetPredicate (n + 1)) :
    BoundedSetPredicate n :=
  .conj (.subset output ambient)
    (.all ambient (.iff (.member (Fin.last n) output.castSucc) p))

/-- Shared extensionality step for reflected definitions of whole output sets. -/
lemma eval_setComprehension_iff_eq {n : ℕ} (ambient output : Fin n)
    (p : BoundedSetPredicate (n + 1)) (xs : Fin n → ZFSet.{u}) (B : ZFSet.{u})
    (hsub : B ⊆ xs ambient)
    (hp : ∀ z ∈ xs ambient, p.eval (Fin.snoc xs z) ↔ z ∈ B) :
    (setComprehension ambient output p).eval xs ↔ xs output = B := by
  simp only [setComprehension, eval, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨hs, he⟩
    ext z
    exact ⟨fun hz => (hp z (hs hz)).mp ((he z (hs hz)).mp hz),
      fun hz => (he z (hsub hz)).mpr ((hp z (hsub hz)).mpr hz)⟩
  · rintro h
    rw [h]
    exact ⟨hsub, fun z hz => (hp z hz).symm⟩

end PolishSpaceBook.SetTheoryModels.BoundedSetPredicate

namespace PolishSpaceBook.SetTheoryModels
open ZFSet BoundedSetPredicate
universe u

def binaryMemberAt {n : ℕ} (G a b c : Fin n) : BoundedSetPredicate n :=
  binaryMember.rename ![G, a, b, c]

lemma eval_binaryMemberAt {n : ℕ} (G a b c : Fin n) (xs : Fin n → ZFSet.{u}) :
    (binaryMemberAt G a b c).eval xs ↔ pair (pair (xs a) (xs b)) (xs c) ∈ xs G := by
  rw [binaryMemberAt, eval_rename]
  have he : xs ∘ ![G, a, b, c] = ![xs G, xs a, xs b, xs c] := by funext i; fin_cases i <;> rfl
  rw [he, eval_binaryMember]

end PolishSpaceBook.SetTheoryModels
