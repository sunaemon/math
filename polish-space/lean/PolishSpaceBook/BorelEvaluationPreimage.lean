module

public import PolishSpaceBook.BorelExpressionEvaluation
public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-! # Transport of Borel evaluations by inverse images -/

namespace PolishSpaceBook.BorelExpression
open Set

/-- Inverse images preserve every node equation, including complementation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Inverse images preserve the empty set and countable unions,
    and convert complements by
    $$i^{-1}(\SetDifference{\BaireSpace}{A})=\SetDifference{\CantorSpace}{i^{-1}(A)}.$$
    Thus $s\mapsto i^{-1}(A_s)$ satisfies exactly the node equations defining $D_s$.
-/
theorem SetEvaluation.preimage {X Y : Type*} {c : BorelExpression}
    {U : ℕ → Set Y} {A : List ℕ → Set Y} (hA : c.SetEvaluation U A) (f : X → Y) :
    c.SetEvaluation (fun n => f ⁻¹' U n) (fun s => f ⁻¹' A s) := by
  intro s
  dsimp only
  rw [hA s]
  split_ifs <;> simp only [preimage_empty, preimage_iUnion, preimage_compl]

/-- Compare the two recursive constructions through their common node equations. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Uniqueness of evaluation by well-founded induction gives the result.
-/
theorem evaluate_preimage {X Y : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set Y) (f : X → Y) (s : List ℕ) :
    f ⁻¹' c.evaluate hw U s = c.evaluate hw (fun n => f ⁻¹' U n) s := by
  exact congrFun ((c.evaluate_isEvaluation hw U).preimage f |>.unique hw
    (c.evaluate_isEvaluation hw (fun n => f ⁻¹' U n))) s

/-- Binary points are natural-number points with every coordinate zero or one. -/
def cantorInclusion (x : ℕ → Bool) : ℕ → ℕ := fun i => (x i).toNat

lemma cantorInclusion_injective : Function.Injective cantorInclusion := by
  intro x y h
  funext i
  have hi := congrFun h i
  cases hx : x i <;> cases hy : y i <;> simp_all [cantorInclusion]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For every finite binary word $w$, the coordinate test gives $i^{-1}(\cyl{\widehat w})=\cyl{w}$,
    where $\widehat w$ is the same word over $\omega$.
-/
lemma cantorInclusion_preimage_cyl (w : List Bool) :
    cantorInclusion ⁻¹' cyl (w.map Bool.toNat) = cyl w := by
  ext x
  change (∀ i (hi : i < (w.map Bool.toNat).length),
    (x i).toNat = (w.map Bool.toNat).get ⟨i, hi⟩) ↔
    ∀ i (hi : i < w.length), x i = w.get ⟨i, hi⟩
  simp only [List.length_map, List.get_eq_getElem, List.getElem_map]
  have hb (a b : Bool) : a.toNat = b.toNat ↔ a = b := by cases a <;> cases b <;> decide
  simp only [hb]

/-- In particular, complements in Cantor space are obtained by restricting Baire complements. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Cantor restriction of Borel evaluations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The random-forcing presentation uses binary sequences rather than arbitrary natural-number sequences.
    Let $i:\CantorSpace\to\BaireSpace$ be the coordinatewise inclusion, and let $b(n)$ be finite binary words.
    Write $\widehat b(n)$ for the same words viewed as natural-number words. For a fixed externally well-founded
    expression $c$, let $A_s$ be its evaluation on $\BaireSpace$ with leaf cylinders $\cyl{\widehat b(n)}$,
    and let $D_s$ be its evaluation on $\CantorSpace$ with leaf cylinders $\cyl{b(n)}$.
    The syntax and child relation are unchanged; only the leaf sets and the ambient space of complements change.
-/
theorem cantor_evaluate (c : BorelExpression) (hw : WellFounded c.Child)
    (b : ℕ → List Bool) (s : List ℕ) :
    cantorInclusion ⁻¹' c.evaluate hw (fun n => cyl ((b n).map Bool.toNat)) s =
      c.evaluate hw (fun n => cyl (b n)) s := by
  rw [c.evaluate_preimage hw _ cantorInclusion s]
  simp only [cantorInclusion_preimage_cyl]

end PolishSpaceBook.BorelExpression
