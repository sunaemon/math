module

public import PolishSpaceBook.BorelInternalLabelFamilies
public import PolishSpaceBook.SetTheoryWordCons

@[expose] public section

/-! # Bounded label descriptions through grafting

This is composition of first-order descriptions of mathematical Borel codes.
It makes no claim of effective selection or of an executable realizer.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

def graftValueRename {k : ℕ} : Fin (k + 3) → Fin (k + 4) :=
  Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin k => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last (k + 2)).castSucc) (Fin.last (k + 3))) (Fin.last (k + 1)).castSucc.castSucc

lemma graftValueRename_values {k : ℕ} (xs : Fin k → ZFSet.{u}) (w y n t : ZFSet.{u}) :
    Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs w) y) n) t ∘ graftValueRename =
      Fin.snoc (Fin.snoc (Fin.snoc xs n) t) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [graftValueRename]
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [graftValueRename]
    · refine Fin.lastCases ?_ (fun j'' => ?_) j'
      · simp [graftValueRename]
      · simp [graftValueRename]

lemma graftConsRename_values {k : ℕ} (xs : Fin k → ZFSet.{u}) (Ω z : Fin k) (w y n t : ZFSet.{u}) :
    Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs w) y) n) t ∘
      ![Ω.castSucc.castSucc.castSucc.castSucc, z.castSucc.castSucc.castSucc.castSucc,
        (Fin.last (k + 2)).castSucc, Fin.last (k + 3), (Fin.last k).castSucc.castSucc.castSucc] =
      ![xs Ω, xs z, n, t, w] := by
  funext i
  fin_cases i <;> simp

/-- Consume the child-index variable of a bounded label description. -/
def graftLabelDescription {k : ℕ} (p : BoundedSetPredicate (k + 3))
    (Ω z W e r : Fin k) : BoundedSetPredicate (k + 2) :=
  .disj (.conj (.equal (Fin.last k).castSucc e.castSucc.castSucc)
      (.equal (Fin.last (k + 1)) r.castSucc.castSucc))
    (.ex Ω.castSucc.castSucc (.ex W.castSucc.castSucc.castSucc
      (.conj (wordConsPredicate.rename ![Ω.castSucc.castSucc.castSucc.castSucc,
        z.castSucc.castSucc.castSucc.castSucc, (Fin.last (k + 2)).castSucc,
        Fin.last (k + 3), (Fin.last k).castSucc.castSucc.castSucc])
        (p.rename graftValueRename))))

theorem eval_graftLabelDescription {k : ℕ} (p : BoundedSetPredicate (k + 3))
    (Ω z W e r : Fin k) (xs : Fin k → ZFSet.{u}) (a : ℕ)
    (hΩ : xs Ω = Ordinal.omega0.toZFSet) (hz : xs z = natOrdinal 0)
    (hW : xs W = finiteSequences) (he : xs e = wordGraph []) (hr : xs r = natOrdinal a)
    (c : ℕ → BorelExpression)
    (hp : ∀ n t y, p.eval (Fin.snoc (Fin.snoc (Fin.snoc xs (natOrdinal n)) (wordGraph t)) y) ↔
      y = natOrdinal (c n t)) (s : List ℕ) (y : ZFSet.{u}) :
    (graftLabelDescription p Ω z W e r).eval (Fin.snoc (Fin.snoc xs (wordGraph s)) y) ↔
      y = natOrdinal (graft a c s) := by
  simp only [graftLabelDescription, eval, eval_rename, graftValueRename_values,
    Fin.snoc_castSucc, Fin.snoc_last, graftConsRename_values]
  change ((wordGraph s = xs e ∧ y = xs r) ∨
    ∃ n ∈ xs Ω, ∃ t ∈ xs W,
      SetWordCons (xs Ω) (xs z) n t (wordGraph s) ∧
      p.eval (Fin.snoc (Fin.snoc (Fin.snoc xs n) t) y)) ↔ _
  rw [hΩ, hz, hW, he, hr, exists_mem_omegaOrdinal]
  simp only [exists_mem_finiteSequences, hp, setWordCons_wordGraph_iff,
    wordGraph_injective.eq_iff]
  cases s with
  | nil => simp [graft]
  | cons n t => simp [graft, List.cons.injEq]

def omitChildRename {k : ℕ} : Fin (k + 2) → Fin (k + 3) :=
  Fin.snoc (Fin.snoc (fun i : Fin k => i.castSucc.castSucc.castSucc)
    (Fin.last (k + 1)).castSucc) (Fin.last (k + 2))

lemma omitChildRename_values {k : ℕ} (xs : Fin k → ZFSet.{u}) (n w y : ZFSet.{u}) :
    Fin.snoc (Fin.snoc (Fin.snoc xs n) w) y ∘ omitChildRename = Fin.snoc (Fin.snoc xs w) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [omitChildRename]
  · refine Fin.lastCases ?_ (fun j' => ?_) j <;> simp [omitChildRename]

/-- Complement keeps child zero and marks the other children absent. -/
def complementLabelDescription {k : ℕ} (p : BoundedSetPredicate (k + 2))
    (Ω z W e two : Fin k) : BoundedSetPredicate (k + 2) :=
  graftLabelDescription
    (.disj (.conj (.equal (Fin.last k).castSucc.castSucc z.castSucc.castSucc.castSucc)
        (p.rename omitChildRename))
      (.conj (.neg (.equal (Fin.last k).castSucc.castSucc z.castSucc.castSucc.castSucc))
        (.equal (Fin.last (k + 2)) z.castSucc.castSucc.castSucc))) Ω z W e two

theorem eval_complementLabelDescription {k : ℕ} (p : BoundedSetPredicate (k + 2))
    (Ω z W e two : Fin k) (xs : Fin k → ZFSet.{u})
    (hΩ : xs Ω = Ordinal.omega0.toZFSet) (hz : xs z = natOrdinal 0)
    (hW : xs W = finiteSequences) (he : xs e = wordGraph []) (htwo : xs two = natOrdinal 2)
    (c : BorelExpression)
    (hp : ∀ s y, p.eval (Fin.snoc (Fin.snoc xs (wordGraph s)) y) ↔ y = natOrdinal (c s))
    (s : List ℕ) (y : ZFSet.{u}) :
    (complementLabelDescription p Ω z W e two).eval (Fin.snoc (Fin.snoc xs (wordGraph s)) y) ↔
      y = natOrdinal (complement c s) := by
  apply eval_graftLabelDescription _ Ω z W e two xs 2 hΩ hz hW he htwo
    (fun n => if n = 0 then c else absent) ?_ s y
  intro n t v
  simp only [eval, Fin.snoc_castSucc, Fin.snoc_last, eval_rename, omitChildRename_values, hz, hp,
    natOrdinal_injective.eq_iff]
  by_cases hn : n = 0 <;> simp [hn, absent]

end PolishSpaceBook.BorelExpression
