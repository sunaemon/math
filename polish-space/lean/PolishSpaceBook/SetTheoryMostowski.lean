module

public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-! # Mostowski collapse by predecessor recursion

The same recursion also supplies the ordinal representation construction.
Injectivity uses induction with the second argument unrestricted; uniqueness
compares recursive equations and then identifies the transitive ranges.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels
universe u v
variable {A : Type v} [Small.{u} A]

/-- The set of already constructed predecessor values. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Define $\pi$ by well-founded recursion:
    $$
    \pi(a)=\{\pi(b): b\,E\,a\}.
    $$
-/
def mostowskiCollapse (r : A → A → Prop) (hw : WellFounded r) : A → ZFSet.{u} :=
  hw.fix (fun a rec => ZFSet.range (fun b : {b : A // r b a} => rec b.val b.property))

theorem mostowskiCollapse_eq (r : A → A → Prop) (hw : WellFounded r) (a : A) :
    mostowskiCollapse r hw a = ZFSet.range (fun b : {b : A // r b a} => mostowskiCollapse r hw b.val) :=
  hw.fix_eq _ a

theorem mem_mostowskiCollapse (r : A → A → Prop) (hw : WellFounded r) (a : A) (z : ZFSet.{u}) :
    z ∈ mostowskiCollapse r hw a ↔ ∃ b, r b a ∧ mostowskiCollapse r hw b = z := by
  rw [mostowskiCollapse_eq, ZFSet.mem_range]
  exact ⟨fun ⟨b, hb⟩ => ⟨b.val, b.property, hb⟩, fun ⟨b, hb, he⟩ => ⟨⟨b, hb⟩, he⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    To prove injectivity, use well-founded induction on $a$, keeping $a'$ arbitrary, to show that
    $\pi(a)=\pi(a')$ implies $a=a'$. If $b\,E\,a$, the recursive equation gives some $c\,E\,a'$ with
    $\pi(b)=\pi(c)$; the induction hypothesis at $b$ gives $b=c$, hence $b\,E\,a'$.
    Conversely, if $b\,E\,a'$, there is some $c\,E\,a$ with $\pi(c)=\pi(b)$, and the induction hypothesis
    at $c$ gives $c=b$, hence $b\,E\,a$. Extensionality now gives $a=a'$.
-/
theorem mostowskiCollapse_injective (r : A → A → Prop) (hw : WellFounded r)
    (hext : Function.Injective (fun a => {b | r b a})) : Function.Injective (mostowskiCollapse r hw) := by
  intro a
  induction a using hw.induction with
  | h a ih =>
    intro a' he
    apply hext
    ext b
    constructor
    · intro hb
      have hm := (mem_mostowskiCollapse r hw a _).mpr ⟨b, hb, rfl⟩
      rw [he] at hm
      obtain ⟨c, hc, hcb⟩ := (mem_mostowskiCollapse r hw a' _).mp hm
      exact (ih b hb hcb.symm) ▸ hc
    · intro hb
      have hm := (mem_mostowskiCollapse r hw a' _).mpr ⟨b, hb, rfl⟩
      rw [← he] at hm
      obtain ⟨c, hc, hcb⟩ := (mem_mostowskiCollapse r hw a _).mp hm
      exact (ih c hc hcb) ▸ hc

theorem mostowskiCollapse_mem_iff (r : A → A → Prop) (hw : WellFounded r)
    (hext : Function.Injective (fun a => {b | r b a})) (a b : A) :
    mostowskiCollapse r hw a ∈ mostowskiCollapse r hw b ↔ r a b := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := (mem_mostowskiCollapse r hw b _).mp h
    exact (mostowskiCollapse_injective r hw hext he) ▸ hc
  · intro h
    exact (mem_mostowskiCollapse r hw b _).mpr ⟨a, h, rfl⟩

def mostowskiImage (r : A → A → Prop) (hw : WellFounded r) : ZFSet.{u} :=
  ZFSet.range (mostowskiCollapse r hw)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Since $A$ is a set, every predecessor collection is a set, and Replacement makes the recursive images sets.
    In particular, $M=\{\pi(a):a\in A\}$ is a set. It is transitive, because every element of $\pi(a)$ is some
    $\pi(b)$ with $b\,E\,a$.
-/
theorem mostowskiImage_transitive (r : A → A → Prop) (hw : WellFounded r) :
    (mostowskiImage r hw).IsTransitive := by
  intro x hx z hz
  obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hx
  obtain ⟨b, _, rfl⟩ := (mem_mostowskiCollapse r hw a _).mp hz
  exact ZFSet.mem_range_self b

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The recursive equation and injectivity show that $b\,E\,a$ iff $\pi(b)\in\pi(a)$, so $\pi$ is an
    isomorphism onto $M$.
-/
def mostowskiIso (r : A → A → Prop) (hw : WellFounded r)
    (hext : Function.Injective (fun a => {b | r b a})) :
    r ≃r (fun x y : mostowskiImage r hw => x.val ∈ y.val) where
  toFun a := ⟨mostowskiCollapse r hw a, ZFSet.mem_range_self a⟩
  invFun x := Classical.choose (ZFSet.mem_range.mp x.property)
  left_inv a := mostowskiCollapse_injective r hw hext (Classical.choose_spec (ZFSet.mem_range.mp
    (ZFSet.mem_range_self a : mostowskiCollapse r hw a ∈ mostowskiImage r hw)))
  right_inv x := Subtype.ext (Classical.choose_spec (ZFSet.mem_range.mp x.property))
  map_rel_iff' := mostowskiCollapse_mem_iff r hw hext _ _

theorem mostowskiCollapse_unique (r : A → A → Prop) (hw : WellFounded r) (f : A → ZFSet.{u})
    (hf : ∀ a, f a = ZFSet.range (fun b : {b : A // r b a} => f b.val)) :
    ∀ a, f a = mostowskiCollapse r hw a := by
  intro a
  induction a using hw.induction with
  | h a ih =>
    rw [hf a, mostowskiCollapse_eq]
    congr 1
    funext b
    exact ih b.val b.property

/-- Every isomorphism onto a transitive set satisfies the same recursive equation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    For uniqueness, let $\rho:(A,E)\cong(N,\in)$ be any isomorphism onto a transitive set.
    Every element of $\rho(a)$ belongs to $N$ by transitivity, so surjectivity and preservation of the relation give
    $$\rho(a)=\{\rho(b):b\,E\,a\}.$$
    Well-founded induction in the two recursive equations gives $\rho(a)=\pi(a)$ for every $a\in A$.
-/
theorem transitive_relIso_eq_collapse (r : A → A → Prop) (hw : WellFounded r)
    {M : ZFSet.{u}} (hM : M.IsTransitive) (e : r ≃r (fun x y : M => x.val ∈ y.val)) :
    ∀ a, (e a).val = mostowskiCollapse r hw a := by
  apply mostowskiCollapse_unique
  intro a
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · intro hz
    have hzM := hM.mem_trans hz (e a).property
    obtain ⟨b, hb⟩ := e.surjective ⟨z, hzM⟩
    have hval : (e b).val = z := congrArg Subtype.val hb
    have hba : r b a := e.map_rel_iff.mp (hval ▸ hz)
    exact ⟨⟨b, hba⟩, hval⟩
  · rintro ⟨b, rfl⟩
    exact e.map_rel_iff.mpr b.property

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Taking images gives $N=M$, proving uniqueness of both the transitive set and the isomorphism.
    \end{proof}
-/
theorem mostowski_representations_agree (r : A → A → Prop) (hw : WellFounded r)
    {M N : ZFSet.{u}} (hM : M.IsTransitive) (hN : N.IsTransitive)
    (e : r ≃r (fun x y : M => x.val ∈ y.val)) (f : r ≃r (fun x y : N => x.val ∈ y.val)) :
    M = N ∧ ∀ a, (e a).val = (f a).val := by
  have h : ∀ a, (e a).val = (f a).val := fun a =>
    (transitive_relIso_eq_collapse r hw hM e a).trans (transitive_relIso_eq_collapse r hw hN f a).symm
  refine ⟨?_, h⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
    have hz' : (f a).val = z := (h a).symm.trans (congrArg Subtype.val ha)
    exact hz' ▸ (f a).property
  · intro hz
    obtain ⟨a, ha⟩ := f.surjective ⟨z, hz⟩
    have hz' : (e a).val = z := (h a).trans (congrArg Subtype.val ha)
    exact hz' ▸ (e a).property

theorem mostowskiIso_unique (r : A → A → Prop) (hw : WellFounded r)
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (e f : r ≃r (fun x y : M => x.val ∈ y.val)) : e = f := by
  apply DFunLike.ext
  intro a
  exact Subtype.ext ((transitive_relIso_eq_collapse r hw hM e a).trans
    (transitive_relIso_eq_collapse r hw hM f a).symm)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Mostowski collapse
-/
theorem mostowski_collapse (r : A → A → Prop) (hw : WellFounded r)
    (hext : Function.Injective (fun a => {b | r b a})) :
    ∃! M : ZFSet.{u}, M.IsTransitive ∧ ∃! _e : r ≃r (fun x y : M => x.val ∈ y.val), True := by
  refine ⟨mostowskiImage r hw, ⟨mostowskiImage_transitive r hw, ⟨mostowskiIso r hw hext, trivial, ?_⟩⟩, ?_⟩
  · intro e _
    exact mostowskiIso_unique r hw (mostowskiImage_transitive r hw) e (mostowskiIso r hw hext)
  rintro M ⟨hM, e, _, _⟩
  exact (mostowski_representations_agree r hw hM (mostowskiImage_transitive r hw)
    e (mostowskiIso r hw hext)).1

end PolishSpaceBook.SetTheoryModels
