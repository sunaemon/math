module

public import PolishSpaceBook.SetTheoryPredicateComposition

@[expose] public section

/-! # Bounded descriptions of entire function graphs

A bounded value relation determines a bounded graph relation once its domain
and codomain are named. This lets later Replacement arguments collect whole
families of graphs, rather than merely proving separate membership of values.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.BoundedSetPredicate
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Insert the candidate graph before the two value variables. -/
def graphValueRename {n : ℕ} : Fin (n + 2) → Fin (n + 3) :=
  Fin.snoc (Fin.snoc (fun i : Fin n => i.castSucc.castSucc.castSucc)
    (Fin.last (n + 1)).castSucc) (Fin.last (n + 2))

lemma graphValueRename_values {n : ℕ} (xs : Fin n → ZFSet.{u}) (G x y : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs G) x) y) ∘ graphValueRename =
      Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [graphValueRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [graphValueRename]
    · simp [graphValueRename]

/-- Parameters are the value relation's parameters followed by the candidate graph. -/
def graph {n : ℕ} (p : BoundedSetPredicate (n + 2)) (a b : Fin n) :
    BoundedSetPredicate (n + 1) :=
  .conj (.function a.castSucc b.castSucc (Fin.last n))
    (.all a.castSucc (.all b.castSucc.castSucc
      (.iff (.pairMember (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)))
        (p.rename graphValueRename))))

lemma eval_graph {n : ℕ} (p : BoundedSetPredicate (n + 2)) (a b : Fin n)
    (xs : Fin n → ZFSet.{u}) (G : ZFSet.{u}) :
    (p.graph a b).eval (Fin.snoc xs G) ↔
      IsFunc (xs a) (xs b) G ∧ ∀ x ∈ xs a, ∀ y ∈ xs b,
        (pair x y ∈ G ↔ p.eval (Fin.snoc (Fin.snoc xs x) y)) := by
  simp only [graph, eval, Fin.snoc_castSucc, Fin.snoc_last, eval_rename,
    graphValueRename_values]

/-- A value description of a known total graph also uniquely describes the whole graph. -/
theorem eval_graph_iff_eq {n : ℕ} (p : BoundedSetPredicate (n + 2)) (a b : Fin n)
    (xs : Fin n → ZFSet.{u}) (G₀ G : ZFSet.{u})
    (hG₀ : IsFunc (xs a) (xs b) G₀)
    (hp : ∀ x ∈ xs a, ∀ y ∈ xs b,
      p.eval (Fin.snoc (Fin.snoc xs x) y) ↔ pair x y ∈ G₀) :
    (p.graph a b).eval (Fin.snoc xs G) ↔ G = G₀ := by
  rw [eval_graph]
  constructor
  · rintro ⟨hG, h⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (hG.1 hz)
      exact (hp x hx y hy).mp ((h x hx y hy).mp hz)
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (hG₀.1 hz)
      exact (h x hx y hy).mpr ((hp x hx y hy).mpr hz)
  · rintro rfl
    exact ⟨hG₀, fun x hx y hy => (hp x hx y hy).symm⟩

end PolishSpaceBook.SetTheoryModels.BoundedSetPredicate
