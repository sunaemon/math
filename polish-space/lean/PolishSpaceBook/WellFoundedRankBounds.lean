module

public import PolishSpaceBook.WellFoundedRankMaps

@[expose] public section

/-! # Testing an accessible-node rank against a well-founded bound

The source relation need not be well founded globally. A bound includes local
accessibility; the recursion therefore excludes infinite branches, rather than
assigning an ordinal to a node before its well-foundedness is known.
-/
namespace PolishSpaceBook
namespace RankBound

/-- Accessibility together with a bound on the canonical accessible-node rank. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Let $\RankLayer{a}{s}$ be the set of $x$ for which the restriction of $E_x$ to nodes reachable from $s$
    by finitely many downward steps is well founded, and the rank at $s$ is at most $r(a)$. The rank at $s$ is used only
    when that part is well founded; no ordinal
    rank is assigned to a node above an infinite descending chain.
-/
def Holds {α β : Type} (R : β → β → Prop) (hR : WellFounded R)
    (E : α → α → Prop) (a : β) (s : α) : Prop :=
  ∃ hs : Acc E s, hs.rank ≤ (hR.apply a).rank

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Bounded-rank recursion
  excerpt: |
    For every $a,s$,
    $$\RankLayer{a}{s}
     =\bigcap_{t\in\NN}\left(E_{t,s}^{\complement}\cup
           \bigcup_{b:\,R(b,a)}\RankLayer{b}{t}\right).$$
    In particular, if $a$ has no $R$-predecessor, this is the set of $x$ for which $s$ has no $E_x$-predecessor.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Suppose $x\in\RankLayer{a}{s}$ and $E_x(t,s)$. The rank of $t$ is strictly less than the rank of $s$,
    and hence strictly less than $r(a)$. Since
    $$r(a)=\sup_{b:\,R(b,a)}(r(b)+1),$$
    there is $b$ with $R(b,a)$ and the rank of $t$ at most $r(b)$. Thus $x\in\RankLayer{b}{t}$.
    This proves inclusion in the displayed right-hand side.

    Conversely, suppose $x$ belongs to that right-hand side. For every $E_x$-predecessor $t$ of $s$, there is $b$
    with $R(b,a)$ and $x\in\RankLayer{b}{t}$. Thus every such $t$ has a well-founded relation below it,
    which proves the same for $s$. The successor of the rank of $t$ is at most $r(b)+1$, and this is at
    most $r(a)$. Taking the supremum over the predecessors of $s$ proves the rank bound at $s$.
    If $a$ has no predecessor, the inner union is empty, giving the last assertion.
-/
theorem iff_children {α β : Type} (R : β → β → Prop) (hR : WellFounded R)
    (E : α → α → Prop) (a : β) (s : α) :
    Holds R hR E a s ↔ ∀ t, E t s → ∃ b, R b a ∧ Holds R hR E b t := by
  constructor
  · rintro ⟨hs, hle⟩ t ht
    have hlt := (Acc.rank_lt_of_rel hs ht).trans_le hle
    rw [(hR.apply a).rank_eq, Ordinal.lt_iSup_iff] at hlt
    obtain ⟨⟨b,hb⟩, hlt⟩ := hlt
    exact ⟨b,hb,hs.inv ht,Order.lt_succ_iff.mp hlt⟩
  · intro h
    have hs : Acc E s := by
      constructor
      intro t ht
      obtain ⟨b,hb,hacc,hbound⟩ := h t ht
      exact hacc
    refine ⟨hs,?_⟩
    rw [hs.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨t,ht⟩
    obtain ⟨b,hb,hacc,hbound⟩ := h t ht
    refine (Order.succ_le_succ hbound).trans ?_
    rw [(hR.apply a).rank_eq]
    exact Ordinal.le_iSup
      (fun v : {v // R v a} => Order.succ ((hR.apply a).inv v.property).rank) ⟨b,hb⟩

theorem mono {α β : Type} {R : β → β → Prop} {hR : WellFounded R}
    {E : α → α → Prop} {a b : β} {s : α}
    (h : Holds R hR E a s) (hab : (hR.apply a).rank ≤ (hR.apply b).rank) :
    Holds R hR E b s := by
  obtain ⟨hs,ha⟩ := h
  exact ⟨hs,ha.trans hab⟩

theorem minimal_iff {α β : Type} (R : β → β → Prop) (hR : WellFounded R)
    (E : α → α → Prop) (a : β) (s : α) (ha : ∀ b, ¬ R b a) :
    Holds R hR E a s ↔ ∀ t, ¬ E t s := by
  rw [iff_children]
  simp only [ha, false_and, exists_false, imp_false]

end RankBound
end PolishSpaceBook
