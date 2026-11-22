module

public import Mathlib.Order.PFilter

@[expose] public section

/-! # Transporting a filter along an order embedding by upward closure -/

namespace PolishSpaceBook
variable {P Q : Type*} [Preorder P] [Preorder Q]

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The image is nonempty, and its upward closure is upward closed.
    For two members of that closure, choose preimages in the filter below them. A common strengthening
    of the preimages maps to a common strengthening in the closure, proving directedness.
    If $e(a)$ belongs to the closure, some $b\in G$ satisfies $e(b)\le e(a)$.
    Order reflection gives $b\le a$, so upward closure of $G$ gives $a\in G$.
    The converse follows directly from the definition.
-/
/-- The upward closure of the image, retaining all information on the embedded order. -/
def transportPFilter (e : P ↪o Q) (G : Order.PFilter P) : Order.PFilter Q :=
  (Order.IsPFilter.of_def (F := {q | ∃ p ∈ G, e p ≤ q})
    (by obtain ⟨p, hp⟩ := G.nonempty; exact ⟨e p, p, hp, le_rfl⟩)
    (by
      rintro q ⟨p, hp, hpq⟩ s ⟨r, hr, hrs⟩
      obtain ⟨t, ht, htp, htr⟩ := G.directed p hp r hr
      exact ⟨e t, ⟨t, ht, le_rfl⟩, (e.monotone htp).trans hpq, (e.monotone htr).trans hrs⟩)
    (by rintro q s hqs ⟨p, hp, hpq⟩; exact ⟨p, hp, hpq.trans hqs⟩)).toPFilter

lemma mem_transportPFilter (e : P ↪o Q) (G : Order.PFilter P) (q : Q) :
    q ∈ transportPFilter e G ↔ ∃ p ∈ G, e p ≤ q := Iff.rfl

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Transporting filters through an order embedding
-/
theorem image_mem_transportPFilter (e : P ↪o Q) (G : Order.PFilter P) (p : P) :
    e p ∈ transportPFilter e G ↔ p ∈ G := by
  rw [mem_transportPFilter]
  exact ⟨fun ⟨q, hq, hqp⟩ => G.mem_of_le (e.le_iff_le.mp hqp) hq, fun hp => ⟨p, hp, le_rfl⟩⟩

end PolishSpaceBook
