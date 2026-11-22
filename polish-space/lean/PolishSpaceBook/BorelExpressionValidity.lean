module

public import PolishSpaceBook.BorelExpressionCertificates
public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Order.WellFounded

@[expose] public section

/-!
# Coanalytic validity of external Borel expression trees

Ill-foundedness has a closed descending-chain witness relation. The remaining
syntax conditions form a Borel set. Thus invalidity is analytic uniformly
in the external real code. This does not yet prove a lightface classification
of natural-number indices for oracle-recursive expression trees.
-/

namespace PolishSpaceBook
namespace BorelExpression
open Set MeasureTheory TopologicalSpace

/-- Structural syntax separated from well-foundedness. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The labels are zero for an absent node, one for a union, two for a complement, and numbers at least
    three for basic-cylinder leaves. The structural conditions require a present root, prefix closure of
    present nodes, no children at a leaf, a present child at a union, and exactly one present child at a
    complement. Well-foundedness means that there is no infinite chain of present children. In this section,
    the label program is total jointly in the family index and the word code at the fixed parameter.
-/
def Syntax (c : BorelExpression) : Prop :=
  c [] ≠ 0 ∧
  (∀ s k, c (s ++ [k]) ≠ 0 → c s ≠ 0) ∧
  (∀ s, 3 ≤ c s → ∀ k, c (s ++ [k]) = 0) ∧
  (∀ s, c s = 1 → ∃ k, c (s ++ [k]) ≠ 0) ∧
  (∀ s, c s = 2 → ∃! k, c (s ++ [k]) ≠ 0)


theorem valid_iff_syntax_wellFounded (c : BorelExpression) :
    c.Valid ↔ c.Syntax ∧ WellFounded c.Child := by
  simp only [Valid, Syntax]
  tauto

/-- Immediate-parent closure gives closure under every finite prefix. -/
theorem Syntax.present_prefix {c : BorelExpression} (hc : c.Syntax)
    {s t : List ℕ} (ht : c t ≠ 0) (hst : s <+: t) : c s ≠ 0 := by
  obtain ⟨u, rfl⟩ := hst
  induction u using List.reverseRecOn with
  | nil => simpa using ht
  | append_singleton u k ih =>
    apply ih
    apply hc.2.1 (s ++ u) k
    simpa only [List.append_assoc] using ht

/-- A child chain may start below the root. Prefix closure fills in its finite
initial segment, yielding a branch from the root. -/
theorem Syntax.branch_of_child_chain {c : BorelExpression} (hc : c.Syntax)
    (f : ℕ → List ℕ) (hf : ∀ n, c.Child (f (n + 1)) (f n)) :
    ∃ x : baire_space, ∀ n, c (seqPrefix x n) ≠ 0 := by
  have hstep (n : ℕ) : f n <+: f (n + 1) := by
    obtain ⟨k, hk, _⟩ := (hf n).2
    rw [hk]
    exact List.prefix_append _ _
  have hp (m n : ℕ) (hmn : m ≤ n) : f m <+: f n := by
    induction n, hmn using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ n _ ih => exact ih.trans (hstep n)
  have hlen (n : ℕ) : n ≤ (f n).length := by
    induction n with
    | zero => omega
    | succ n ih =>
      obtain ⟨k, hk, _⟩ := (hf n).2
      simp only [hk, List.length_append, List.length_singleton]
      omega
  let x : baire_space := fun i => (f (i + 1))[i]'(by have := hlen (i + 1); omega)
  refine ⟨x, fun n => ?_⟩
  have heq : seqPrefix x n = (f n).take n := by
    apply List.ext_getElem
    · simp [seqPrefix_length, List.length_take, Nat.min_eq_left (hlen n)]
    · intro i hi hi'
      have hin : i < n := by simpa only [seqPrefix_length] using hi
      simp only [seqPrefix, List.getElem_ofFn, List.getElem_take]
      exact (hp (i + 1) n (by omega)).getElem (by have := hlen (i + 1); omega)
  rw [heq]
  exact hc.present_prefix (hf n).1 (List.take_prefix n _)

/-- With the local syntax rules, absence of a branch from the root is exactly
well-foundedness of the immediate-child relation on all finite positions. -/
theorem Syntax.wellFounded_iff_no_branch {c : BorelExpression} (hc : c.Syntax) :
    WellFounded c.Child ↔ ∀ x : baire_space, ∃ n, c (seqPrefix x n) = 0 := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  · intro hw x
    by_contra h
    push Not at h
    apply hw.false
    refine ⟨fun n => seqPrefix x n, fun n => ⟨h n, x n, ?_, h (n + 1)⟩⟩
    exact seqPrefix_succ_eq_concat x n
  · intro h
    refine ⟨fun ⟨f, hf⟩ => ?_⟩
    obtain ⟨x, hx⟩ := hc.branch_of_child_chain f hf
    obtain ⟨n, hn⟩ := h x
    exact hx n hn

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Let $\BorelCodes \IncludedIn \BaireSpace$ be the set of valid external records of Borel codes.
    Besides the local recording rules, validity requires that following immediate subcodes cannot continue indefinitely:
    $$\forall x \in \BaireSpace\ \exists n\ c(\FiniteSequenceCode{\restrict{x}{n}})=0.$$
    Here $x$ specifies successive choices of subcode numbers.
-/
theorem valid_iff_syntax_no_branch (c : BorelExpression) :
    c.Valid ↔ c.Syntax ∧ ∀ x : baire_space, ∃ n, c (seqPrefix x n) = 0 := by
  rw [valid_iff_syntax_wellFounded]
  exact and_congr_right fun hc => hc.wellFounded_iff_no_branch

private theorem measurable_forall {Z I : Type*} [MeasurableSpace Z] [Countable I]
    {p : I → Z → Prop} (h : ∀ i, MeasurableSet {z | p i z}) :
    MeasurableSet {z | ∀ i, p i z} := by
  simpa only [ofPred_forall] using MeasurableSet.iInter h

private theorem measurable_exists {Z I : Type*} [MeasurableSpace Z] [Countable I]
    {p : I → Z → Prop} (h : ∀ i, MeasurableSet {z | p i z}) :
    MeasurableSet {z | ∃ i, p i z} := by
  simpa only [ofPred_exists] using MeasurableSet.iUnion h

private theorem measurable_imp {Z : Type*} [MeasurableSpace Z] {p q : Z → Prop}
    (hp : MeasurableSet {z | p z}) (hq : MeasurableSet {z | q z}) :
    MeasurableSet {z | p z → q z} := by
  convert hp.compl.union hq using 1
  ext z
  simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]

theorem measurableSet_syntax : MeasurableSet {c : BorelExpression | c.Syntax} := by
  have hc (s : List ℕ) (n : ℕ) : MeasurableSet {c : BorelExpression | c s = n} :=
    ((isClopen_discrete {n}).preimage (continuous_apply s)).isClosed.measurableSet
  have hl (s : List ℕ) : MeasurableSet {c : BorelExpression | 3 ≤ c s} :=
    ((isClopen_discrete {n : ℕ | 3 ≤ n}).preimage (continuous_apply s)).isClosed.measurableSet
  refine (hc [] 0).compl.inter ?_
  refine (measurable_forall (fun s => measurable_forall (fun k =>
    measurable_imp (hc (s ++ [k]) 0).compl (hc s 0).compl))).inter ?_
  refine (measurable_forall (fun s => measurable_imp (hl s)
    (measurable_forall (fun k => hc (s ++ [k]) 0)))).inter ?_
  refine (measurable_forall (fun s => measurable_imp (hc s 1)
    (measurable_exists (fun k => (hc (s ++ [k]) 0).compl)))).inter ?_
  apply measurable_forall
  intro s
  apply measurable_imp (hc s 2)
  change MeasurableSet {c : BorelExpression | ∃ k, c (s ++ [k]) ≠ 0 ∧
    ∀ j, c (s ++ [j]) ≠ 0 → j = k}
  apply measurable_exists
  intro k
  apply (hc (s ++ [k]) 0).compl.inter
  apply measurable_forall
  intro j
  apply measurable_imp (hc (s ++ [j]) 0).compl
  by_cases h : j = k <;> simp [h]

/-- No rank is assumed: a descending chain itself witnesses invalidity. -/
theorem analyticSet_not_wellFounded :
    AnalyticSet {c : BorelExpression | ¬ WellFounded c.Child} := by
  classical
  let : TopologicalSpace (List ℕ) := ⊥
  let : DiscreteTopology (List ℕ) := ⟨rfl⟩
  let : PolishSpace (List ℕ) := inferInstance
  let S := {z : BorelExpression × (ℕ → List ℕ) | ∀ n, z.1.Child (z.2 (n + 1)) (z.2 n)}
  have hchild (s t : List ℕ) : IsClopen {z : BorelExpression × (ℕ → List ℕ) | z.1.Child t s} := by
    by_cases he : ∃ k, t = s ++ [k]
    · have heq : {z : BorelExpression × (ℕ → List ℕ) | z.1.Child t s} =
          {z | z.1 s ≠ 0} ∩ {z | z.1 t ≠ 0} := by
        ext z
        simp only [Child, mem_ofPred_eq, mem_inter_iff]
        obtain ⟨k, hk⟩ := he
        aesop
      rw [heq]
      exact ((isClopen_discrete {0}).preimage ((continuous_apply s).comp continuous_fst)).compl.inter
        ((isClopen_discrete {0}).preimage ((continuous_apply t).comp continuous_fst)).compl
    · have heq : {z : BorelExpression × (ℕ → List ℕ) | z.1.Child t s} = ∅ := by
        ext z
        simp only [Child, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ k hk _
        exact he ⟨k, hk⟩
      rw [heq]
      exact isClopen_empty
  have hs : IsClosed S := by
    have heq : S = {z : BorelExpression × (ℕ → List ℕ) |
        ∀ n s t, z.2 n = s → z.2 (n + 1) = t → z.1.Child t s} := by
      ext z
      constructor
      · intro hz n s t hn ht
        simpa [hn, ht] using hz n
      · intro hz n
        exact hz n (z.2 n) (z.2 (n + 1)) rfl rfl
    rw [heq]
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro t
    have hns : IsClopen {z : BorelExpression × (ℕ → List ℕ) | z.2 n = s} :=
      (isClopen_discrete {s}).preimage (by fun_prop)
    have hnt : IsClopen {z : BorelExpression × (ℕ → List ℕ) | z.2 (n + 1) = t} :=
      (isClopen_discrete {t}).preimage (by fun_prop)
    convert (hns.compl.union (hnt.compl.union (hchild s t))).isClosed using 1
    ext z
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  have heq : Prod.fst '' S = {c : BorelExpression | ¬ WellFounded c.Child} := by
    ext c
    simp only [mem_image, mem_ofPred_eq, wellFounded_iff_isEmpty_descending_chain]
    constructor
    · rintro ⟨⟨c, f⟩, hf, rfl⟩ h
      exact h.false ⟨f, hf⟩
    · intro hn
      have hn' : Nonempty {f : ℕ → List ℕ // ∀ n, c.Child (f (n + 1)) (f n)} :=
        not_isEmpty_iff.mp hn
      obtain ⟨⟨f, hf⟩⟩ := hn'
      exact ⟨(c, f), hf, rfl⟩
  rw [← heq]
  exact hs.analyticSet.image_of_continuous continuous_fst

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: proposition
  title: Coanalyticity of valid Borel codes
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: proof
  excerpt: |
    The local syntax conditions are Borel: each refers to finitely many label coordinates, followed by countable
    quantifiers over positions and subcode numbers. Failure of termination is witnessed by a sequence of present positions,
    each specifying an immediate subcode of its predecessor. Give finite words the discrete topology. The relation
    between a code
    and such a sequence is closed, since each successive-subcode condition is clopen and there are countably many of them.
    Its projection is analytic. Invalidity is the union of this projection and the Borel set of syntax failures,
    so invalidity is analytic and validity is coanalytic.
-/
/-- Equivalently, Valid is coanalytic in the space of external real codes. -/
theorem analyticSet_not_valid : AnalyticSet {c : BorelExpression | ¬ c.Valid} := by
  have heq : {c : BorelExpression | ¬ c.Valid} =
      {c : BorelExpression | ¬ c.Syntax} ∪ {c : BorelExpression | ¬ WellFounded c.Child} := by
    ext c
    simp only [mem_ofPred_eq, mem_union, valid_iff_syntax_wellFounded]
    tauto
  rw [heq]
  have h₁ : AnalyticSet {c : BorelExpression | ¬ c.Syntax} := measurableSet_syntax.compl.analyticSet
  have h₂ := analyticSet_not_wellFounded
  have h := AnalyticSet.iUnion (s := fun b : Bool => if b then {c : BorelExpression | ¬ c.Syntax} else {c : BorelExpression | ¬ WellFounded c.Child})
    (fun b => by cases b
                 · simpa using h₂
                 · simpa using h₁)
  have hsets : (⋃ b : Bool, if b then {c : BorelExpression | ¬ c.Syntax}
      else {c : BorelExpression | ¬ WellFounded c.Child}) =
      {c : BorelExpression | ¬ c.Syntax} ∪ {c : BorelExpression | ¬ WellFounded c.Child} := by
    ext c
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact Or.inr hb
      · exact Or.inl hb
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  rwa [hsets] at h

end BorelExpression
end PolishSpaceBook
