module

public import PolishSpaceBook.SetTheoryOrdinalFormulas
public import PolishSpaceBook.SetTheoryFunctionClosure
public import PolishSpaceBook.SetTheoryMostowski

@[expose] public section

/-! # Ordinal representation by the explicit predecessor recursion

The collapse is constructed from its recursive equation, without assuming an
ordinal representation in advance. Internal existence in a ground model is a
separate issue; this file supplies the external construction and rigidity lemmas.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Replace each point of a well-order by the set of values at its predecessors. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    By recursion on $<_W$, define
    $$f(x):=\{f(y):y<_W x\}\qquad(x\in W).$$
    This recursion does not presuppose the representation theorem: the construction in §{sec:ordinals-induction}
    works on predecessor segments of any well-order, using agreement on overlaps and Replacement to collect
    the earlier partial solutions. In particular,
    $$z\in f(x)\quad\Longleftrightarrow\quad
     \exists y<_W x\;z=f(y).$$
    The map is injective. If $x\ne y$, one precedes the other, so one of $f(x),f(y)$ belongs to the other.
    Equality would give a set belonging to itself, contrary to Foundation.
    Consequently the recursive equation also gives
    $$f(x)\in f(y)\quad\Longleftrightarrow\quad x<_W y.$$
    For the reverse implication to the order relation, write $f(x)=f(z)$ with $z<_W y$ and use injectivity.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The representation theorem is obtained by recursion on the given well-order itself.
    We first record the fact that makes the resulting ordinal, and its representing map, unique.
-/
def wellOrderCollapse {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] : W → ZFSet.{u} :=
  mostowskiCollapse r ((inferInstance : WellFounded r))

lemma wellOrderCollapse_eq {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] (x : W) :
    wellOrderCollapse r x = ZFSet.range (fun y : {y : W // r y x} => wellOrderCollapse r y.val) := by
  exact mostowskiCollapse_eq r ((inferInstance : WellFounded r)) x

lemma mem_wellOrderCollapse {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r]
    (x : W) (z : ZFSet.{u}) :
    z ∈ wellOrderCollapse r x ↔ ∃ y : W, r y x ∧ wellOrderCollapse r y = z := by
  rw [wellOrderCollapse_eq, ZFSet.mem_range]
  exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩, fun ⟨y, hr, hy⟩ => ⟨⟨y, hr⟩, hy⟩⟩

lemma wellOrderCollapse_mem_of_rel {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r]
    {x y : W} (hxy : r x y) : wellOrderCollapse r x ∈ wellOrderCollapse r y :=
  (mem_wellOrderCollapse r y _).mpr ⟨x, hxy, rfl⟩

theorem wellOrderCollapse_injective {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] :
    Function.Injective (wellOrderCollapse r) := by
  intro x y he
  rcases trichotomous_of r x y with hxy | heq | hyx
  · exact False.elim (ZFSet.mem_irrefl _ (he ▸ wellOrderCollapse_mem_of_rel r hxy))
  · exact heq
  · exact False.elim (ZFSet.mem_irrefl _ (he.symm ▸ wellOrderCollapse_mem_of_rel r hyx))

lemma wellOrderCollapse_mem_iff {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r]
    (x y : W) : wellOrderCollapse r x ∈ wellOrderCollapse r y ↔ r x y := by
  constructor
  · intro h
    obtain ⟨z, hzy, hz⟩ := (mem_wellOrderCollapse r y _).mp h
    exact (wellOrderCollapse_injective r hz) ▸ hzy
  · exact wellOrderCollapse_mem_of_rel r

/-- Restricting the same collapse gives an isomorphism on every predecessor segment. -/
def wellOrderCollapseInitialIso {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] (x : W) :
    (fun y z : {y : W // r y x} => r y.val z.val) ≃r
      (fun a b : wellOrderCollapse r x => a.val ∈ b.val) := by
  let f : {y : W // r y x} → wellOrderCollapse r x :=
    fun y => ⟨wellOrderCollapse r y.val, wellOrderCollapse_mem_of_rel r y.property⟩
  have hi : Function.Injective f := by
    intro y z he
    exact Subtype.ext (wellOrderCollapse_injective r (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro b
    obtain ⟨y, hy, he⟩ := (mem_wellOrderCollapse r x b.val).mp b.property
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact { Equiv.ofBijective f ⟨hi, hs⟩ with map_rel_iff' := wellOrderCollapse_mem_iff r _ _ }

lemma wellOrderCollapse_isTransitive {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r]
    (x : W) : (wellOrderCollapse r x).IsTransitive := by
  intro z hz t ht
  obtain ⟨y, hyx, rfl⟩ := (mem_wellOrderCollapse r x z).mp hz
  obtain ⟨v, hvy, rfl⟩ := (mem_wellOrderCollapse r y t).mp ht
  exact wellOrderCollapse_mem_of_rel r (trans_of r hvy hyx)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Each $f(x)$ is transitive. Indeed, if $u\in v\in f(x)$, then
    $v=f(y)$ for some $y<_W x$ and $u=f(z)$ for some $z<_W y$.
    Transitivity of $<_W$ gives $z<_W x$, hence $u\in f(x)$.
    Every member of $f(x)$ is itself some $f(y)$ and is therefore transitive as well.
    The transitive-set-of-transitive-sets characterization from §{sec:ordinals-von-neumann} shows that $f(x)$ is an ordinal.
    The restriction of $f$ to $\{y\in W:y<_W x\}$ is an order-isomorphism onto $f(x)$:
    surjectivity is the recursive equation, and the preceding equivalence preserves and reflects the order.
-/
theorem wellOrderCollapse_isOrdinal {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r]
    (x : W) : (wellOrderCollapse r x).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isTransitive.mpr
  refine ⟨wellOrderCollapse_isTransitive r x, ?_⟩
  intro z hz
  obtain ⟨y, _, rfl⟩ := (mem_wellOrderCollapse r x z).mp hz
  exact wellOrderCollapse_isTransitive r y

/-- The image of the predecessor recursion, the representing von Neumann ordinal. -/
def wellOrderOrdinal {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] : ZFSet.{u} :=
  ZFSet.range (wellOrderCollapse r)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    By Replacement, the image
    $$\alpha:=\{f(x):x\in W\}$$
    is a set. The recursive equation makes it transitive, and its members are ordinals, so $\alpha$ is an ordinal.
    The map $f:W\to\alpha$ is bijective and preserves and reflects the order, hence is the required isomorphism.
    For $W=\emptyset$, the construction gives $\alpha=\emptyset$ and the empty function.
-/
theorem wellOrderOrdinal_isOrdinal {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] :
    (wellOrderOrdinal r).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro z hz t ht
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨y, _, rfl⟩ := (mem_wellOrderCollapse r x t).mp ht
    exact ZFSet.mem_range.mpr ⟨y, rfl⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hz
    exact wellOrderCollapse_isOrdinal r x

/-- The explicit collapse is an order isomorphism onto the ordinal it constructs. -/
def wellOrderCollapseIso {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] :
    r ≃r (fun a b : wellOrderOrdinal r => a.val ∈ b.val) where
  toFun x := ⟨wellOrderCollapse r x, ZFSet.mem_range.mpr ⟨x, rfl⟩⟩
  invFun y := Classical.choose (ZFSet.mem_range.mp y.property)
  left_inv x := wellOrderCollapse_injective r (Classical.choose_spec (ZFSet.mem_range.mp
    (ZFSet.mem_range.mpr ⟨x, rfl⟩ : wellOrderCollapse r x ∈ wellOrderOrdinal r)))
  right_inv y := Subtype.ext (Classical.choose_spec (ZFSet.mem_range.mp y.property))
  map_rel_iff' := fun {x y} => wellOrderCollapse_mem_iff r x y

/-- Membership induction rules out downward motion for a membership-preserving self-map. -/
theorem membership_selfmap_not_mem {α : ZFSet.{u}} (g : α → α)
    (hg : ∀ x y : α, x.val ∈ y.val → (g x).val ∈ (g y).val) (x : α) :
    (g x).val ∉ x.val := by
  have h : ∀ a : ZFSet.{u}, ∀ ha : a ∈ α, (g ⟨a, ha⟩).val ∉ a := by
    intro a
    induction a using ZFSet.inductionOn with
    | h a ih =>
      intro ha hga
      have hh := hg (g ⟨a, ha⟩) ⟨a, ha⟩ hga
      exact ih (g ⟨a, ha⟩).val hga (g ⟨a, ha⟩).property hh
  exact h x.val x.property

/-- The book's monotonicity lemma: an increasing ordinal self-map is inflationary. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    If there is a counterexample, let $\delta$ be the least one. Then $g(\delta)<\delta$, so strict increase gives
    $$g(g(\delta))<g(\delta).$$
    Thus $g(\delta)$ is a smaller counterexample, a contradiction.
    Equivalently, membership induction rules out $g(\delta)\in\delta$; ordinal comparison then gives
    $\delta\IncludedIn g(\delta)$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: lemma
  title: Monotonicity of ordinal self-maps
-/
theorem ordinal_selfmap_inflationary {α : ZFSet.{u}} (hα : α.IsOrdinal) (g : α → α)
    (hg : ∀ x y : α, x.val ∈ y.val → (g x).val ∈ (g y).val) (x : α) :
    x.val ⊆ (g x).val :=
  ((hα.mem (g x).property).notMem_iff_subset (hα.mem x.property)).mp (membership_selfmap_not_mem g hg x)

/-- No order-preserving map sends a larger ordinal into one of its elements. -/
theorem no_increasing_map_to_smaller_ordinal {α β : ZFSet.{u}} (hβ : β.IsOrdinal) (hαβ : α ∈ β)
    (g : β → α) (hg : ∀ x y : β, x.val ∈ y.val → (g x).val ∈ (g y).val) : False := by
  let h : β → β := fun x => ⟨(g x).val, hβ.mem_trans (g x).property hαβ⟩
  have hh : ∀ x y : β, x.val ∈ y.val → (h x).val ∈ (h y).val := hg
  exact membership_selfmap_not_mem h hh ⟨α, hαβ⟩ (g ⟨α, hαβ⟩).property

/-- Isomorphic von Neumann ordinals are equal, using the no-downward-motion lemma. -/
theorem ordinal_eq_of_relIso {α β : ZFSet.{u}} (hα : α.IsOrdinal) (hβ : β.IsOrdinal)
    (e : (fun x y : α => x.val ∈ y.val) ≃r (fun x y : β => x.val ∈ y.val)) : α = β := by
  rcases hα.mem_trichotomous hβ with hlt | heq | hgt
  · exact False.elim (no_increasing_map_to_smaller_ordinal hβ hlt e.symm
      (fun x y h => e.symm.map_rel_iff.mpr h))
  · exact heq
  · exact False.elim (no_increasing_map_to_smaller_ordinal hα hgt e
      (fun x y h => e.map_rel_iff.mpr h))

/-- An order automorphism of an ordinal fixes each element. -/
theorem ordinal_relIso_rigid {α : ZFSet.{u}} (hα : α.IsOrdinal)
    (e : (fun x y : α => x.val ∈ y.val) ≃r (fun x y : α => x.val ∈ y.val)) (x : α) :
    (e x).val = x.val := by
  have hx := ordinal_selfmap_inflationary hα e (fun x y h => e.map_rel_iff.mpr h) x
  have he := ordinal_selfmap_inflationary hα e.symm (fun x y h => e.symm.map_rel_iff.mpr h) (e x)
  simp only [RelIso.symm_apply_apply] at he
  exact ZFSet.ext (fun z => ⟨fun hz => he hz, fun hz => hx hz⟩)

/-- Two ordinal representations have the same target and agree at every input. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    For uniqueness of the ordinal, suppose $\alpha<\beta$ and there is an order-isomorphism $g:\beta\to\alpha$.
    Composing with the inclusion into $\beta$ gives a strictly increasing self-map of $\beta$ whose value at
    $\alpha\in\beta$ belongs to $\alpha$. This contradicts the monotonicity lemma.
    Ordinal comparison therefore shows that any two isomorphic ordinals are equal.
    Finally, for an order-automorphism $h:\alpha\to\alpha$, the lemma applied to $h$ and $h^{-1}$ gives
    $$\delta\le h(\delta)\le h^{-1}(h(\delta))=\delta.$$
    Thus $h$ is the identity. Composing one representation with the inverse of another shows that their maps agree
    at every input.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: Ordinal representation theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The representation theorem is obtained by recursion on the given well-order itself.
    We first record the fact that makes the resulting ordinal, and its representing map, unique.
-/
theorem ordinal_representations_agree {W α β : ZFSet.{u}} {r : W → W → Prop}
    (hα : α.IsOrdinal) (hβ : β.IsOrdinal)
    (e : r ≃r (fun x y : α => x.val ∈ y.val)) (f : r ≃r (fun x y : β => x.val ∈ y.val)) :
    α = β ∧ ∀ x : W, (e x).val = (f x).val := by
  have heq := ordinal_eq_of_relIso hα hβ (e.symm.trans f)
  subst β
  refine ⟨rfl, ?_⟩
  intro x
  have hr := ordinal_relIso_rigid hα (e.symm.trans f) (e x)
  simpa only [RelIso.trans_apply, RelIso.symm_apply_apply] using hr.symm

/-- Existence and uniqueness of the representing ordinal, including the empty order. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: Ordinal representation theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
theorem well_order_ordinal_representation {W : ZFSet.{u}} (r : W → W → Prop) [IsWellOrder W r] :
    ∃! α : ZFSet.{u}, α.IsOrdinal ∧ Nonempty (r ≃r (fun x y : α => x.val ∈ y.val)) := by
  refine ⟨wellOrderOrdinal r, ⟨wellOrderOrdinal_isOrdinal r, ⟨wellOrderCollapseIso r⟩⟩, ?_⟩
  rintro α ⟨hα, ⟨e⟩⟩
  exact ordinal_eq_of_relIso hα (wellOrderOrdinal_isOrdinal r) (e.symm.trans (wellOrderCollapseIso r))

end PolishSpaceBook.SetTheoryModels
