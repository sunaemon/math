module

public import PolishSpaceBook.FirstOrderNaturalDeduction

@[expose] public section

/-! # Finite unannotated sequent-labelled trees

A candidate stores only its root sequent and ordered child trees. Local validity
is the seventeen primitive rule schemas, with no rule name, substitution term,
or equality predicate supplied as an annotation in the candidate data.
-/
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
noncomputable local instance unannotatedTreeAlphaDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _

abbrev Sequent (L : Language.{u,v}) := Context L × AlphaFormula L

/-- The original local rule relation on lists of premise sequents. -/
inductive LocalRule : List (Sequent L) → Sequent L → Prop where
  | hyp (Γ : Context L) (φ : AlphaFormula L) (h : φ ∈ Γ) : LocalRule [] (Γ, φ)
  | andIntro (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, φ), (Γ, ψ)] (Γ, binary .conj φ ψ)
  | andLeft (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, binary .conj φ ψ)] (Γ, φ)
  | andRight (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, binary .conj φ ψ)] (Γ, ψ)
  | orLeft (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, φ)] (Γ, binary .disj φ ψ)
  | orRight (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, ψ)] (Γ, binary .disj φ ψ)
  | orElim (Γ : Context L) (φ ψ χ : AlphaFormula L) :
      LocalRule [(Γ, binary .disj φ ψ), (insert φ Γ, χ), (insert ψ Γ, χ)] (Γ, χ)
  | impIntro (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(insert φ Γ, ψ)] (Γ, binary .imp φ ψ)
  | impElim (Γ : Context L) (φ ψ : AlphaFormula L) :
      LocalRule [(Γ, binary .imp φ ψ), (Γ, φ)] (Γ, ψ)
  | falseElim (Γ : Context L) (φ : AlphaFormula L) :
      LocalRule [(Γ, falsum)] (Γ, φ)
  | allIntro (Γ : Context L) (φ : AlphaFormula L) (x : ℕ) (h : x ∉ Γ.fv) :
      LocalRule [(Γ, φ)] (Γ, quant .all x φ)
  | allElim (Γ : Context L) (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
      LocalRule [(Γ, quant .all x φ)] (Γ, φ.subst x t)
  | exIntro (Γ : Context L) (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
      LocalRule [(Γ, φ.subst x t)] (Γ, quant .ex x φ)
  | exElim (Γ : Context L) (φ χ : AlphaFormula L) (x y : ℕ)
      (h : y ∉ Γ.fv ∪ χ.fv ∪ (quant .ex x φ).fv) :
      LocalRule [(Γ, quant .ex x φ), (insert (φ.subst x (.var y)) Γ, χ)] (Γ, χ)
  | eqIntro (Γ : Context L) (t : L.Term ℕ) : LocalRule [] (Γ, equal t t)
  | eqElim (Γ : Context L) (φ : AlphaFormula L) (x : ℕ) (t r : L.Term ℕ) :
      LocalRule [(Γ, φ.subst x t), (Γ, equal t r)] (Γ, φ.subst x r)
  | excludedMiddle (Γ : Context L) (φ : AlphaFormula L) :
      LocalRule [] (Γ, binary .disj φ (neg φ))

/-- The finite input has no inference or substitution annotations. -/
inductive SequentTree (L : Language.{u,v}) where
  | node (root : Sequent L) (children : List (SequentTree L)) : SequentTree L

namespace SequentTree

def root : SequentTree L → Sequent L
  | .node s _ => s

def children : SequentTree L → List (SequentTree L)
  | .node _ cs => cs

/-- All nodes instantiate the printed primitive rules, including their exact contexts. -/
inductive Valid : SequentTree L → Prop where
  | node {s : Sequent L} {cs : List (SequentTree L)} :
      LocalRule (cs.map root) s → (∀ c ∈ cs, Valid c) → Valid (.node s cs)

end SequentTree

/-- Matching a rule really transports derivations of its premises. -/
theorem LocalRule.derives {ps : List (Sequent L)} {s : Sequent L} (h : LocalRule ps s)
    (hp : ∀ p ∈ ps, Derives p.1 p.2) : Derives s.1 s.2 := by
  have premise (Δ : Context L) (ψ : AlphaFormula L) (hm : (Δ, ψ) ∈ ps) : Derives Δ ψ := hp _ hm
  clear hp
  cases h with
  | hyp Γ φ h => exact .assumption h
  | andIntro Γ φ ψ => exact .andIntro (premise _ _ (by simp)) (premise _ _ (by simp))
  | andLeft Γ φ ψ => exact .andLeft (premise Γ (binary .conj φ ψ) (by simp))
  | andRight Γ φ ψ => exact .andRight (premise Γ (binary .conj φ ψ) (by simp))
  | orLeft Γ φ ψ => exact .orLeft ψ (premise _ _ (by simp))
  | orRight Γ φ ψ => exact .orRight φ (premise _ _ (by simp))
  | orElim Γ φ ψ χ =>
    exact .orElim (premise Γ (binary .disj φ ψ) (by simp))
      (premise (insert φ Γ) χ (by simp)) (premise (insert ψ Γ) χ (by simp))
  | impIntro Γ φ ψ => exact .impIntro (premise _ _ (by simp))
  | impElim Γ φ ψ => exact .impElim (premise Γ (binary .imp φ ψ) (by simp)) (premise Γ φ (by simp))
  | falseElim Γ φ => exact .falseElim φ (premise _ _ (by simp))
  | allIntro Γ φ x h => exact .allIntro x (premise _ _ (by simp)) h
  | allElim Γ φ x t => exact .allElim x φ t (premise _ _ (by simp))
  | exIntro Γ φ x t => exact .exIntro x φ t (premise _ _ (by simp))
  | exElim Γ φ χ x y h => exact .exElim x y φ χ (premise _ _ (by simp)) (premise _ _ (by simp)) h
  | eqIntro Γ t => exact .eqIntro Γ t
  | eqElim Γ φ x t r => exact .eqElim φ x t r (premise _ _ (by simp)) (premise _ _ (by simp))
  | excludedMiddle Γ φ => exact .excludedMiddle Γ φ

/-- Local validity of an unannotated tree implies the existing derivability relation. -/
theorem SequentTree.Valid.derives {T : SequentTree L} (h : T.Valid) :
    Derives T.root.1 T.root.2 := by
  induction h with
  | @node s cs hr hc ih =>
    apply hr.derives
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact ih c hc

private theorem one_valid {T : SequentTree L} (h : T.Valid) :
    ∀ c ∈ [T], c.Valid := by simpa only [List.mem_singleton, forall_eq] using h

private theorem two_valid {S T : SequentTree L} (hs : S.Valid) (ht : T.Valid) :
    ∀ c ∈ [S, T], c.Valid := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption

/-- Every existing derivation has an unannotated finite tree. Quotient representatives
and numerical syntax are handled by the separate encoding layer. -/
theorem Derives.exists_valid_tree {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ) :
    ∃ T : SequentTree L, T.root = (Γ, φ) ∧ T.Valid := by
  induction h with
  | hyp Γ φ => exact ⟨.node _ [], rfl, .node (.hyp _ _ (by simp)) (by simp)⟩
  | andIntro h₁ h₂ ih₁ ih₂ =>
    obtain ⟨S, hs, hvS⟩ := ih₁; obtain ⟨T, ht, hvT⟩ := ih₂
    exact ⟨.node _ [S,T], rfl, .node (by simpa [hs, ht] using LocalRule.andIntro _ _ _) (two_valid hvS hvT)⟩
  | andLeft h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.andLeft _ _ _) (one_valid hv)⟩
  | andRight h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.andRight _ _ _) (one_valid hv)⟩
  | orLeft ψ h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.orLeft _ _ ψ) (one_valid hv)⟩
  | orRight φ h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.orRight _ φ _) (one_valid hv)⟩
  | orElim h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    obtain ⟨S, hs, hvS⟩ := ih₁; obtain ⟨T, ht, hvT⟩ := ih₂; obtain ⟨U, hu, hvU⟩ := ih₃
    refine ⟨.node _ [S,T,U], rfl, .node (by simpa [hs, ht, hu] using LocalRule.orElim _ _ _ _) ?_⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  | impIntro h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.impIntro _ _ _) (one_valid hv)⟩
  | impElim h₁ h₂ ih₁ ih₂ =>
    obtain ⟨S, hs, hvS⟩ := ih₁; obtain ⟨T, ht, hvT⟩ := ih₂
    exact ⟨.node _ [S,T], rfl, .node (by simpa [hs, ht] using LocalRule.impElim _ _ _) (two_valid hvS hvT)⟩
  | falseElim φ h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.falseElim _ φ) (one_valid hv)⟩
  | allIntro x h hx ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.allIntro _ _ x hx) (one_valid hv)⟩
  | allElim x φ t h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.allElim _ φ x t) (one_valid hv)⟩
  | exIntro x φ t h ih =>
    obtain ⟨T, ht, hv⟩ := ih
    exact ⟨.node _ [T], rfl, .node (by simpa [ht] using LocalRule.exIntro _ φ x t) (one_valid hv)⟩
  | exElim x y φ χ h₁ h₂ hy ih₁ ih₂ =>
    obtain ⟨S, hs, hvS⟩ := ih₁; obtain ⟨T, ht, hvT⟩ := ih₂
    exact ⟨.node _ [S,T], rfl, .node (by simpa [hs, ht] using LocalRule.exElim _ φ χ x y hy) (two_valid hvS hvT)⟩
  | eqIntro Γ t => exact ⟨.node _ [], rfl, .node (.eqIntro Γ t) (by simp)⟩
  | eqElim φ x t r h₁ h₂ ih₁ ih₂ =>
    obtain ⟨S, hs, hvS⟩ := ih₁; obtain ⟨T, ht, hvT⟩ := ih₂
    exact ⟨.node _ [S,T], rfl, .node (by simpa [hs, ht] using LocalRule.eqElim _ φ x t r) (two_valid hvS hvT)⟩
  | excludedMiddle Γ φ => exact ⟨.node _ [], rfl, .node (.excludedMiddle Γ φ) (by simp)⟩

/-- This equivalence concerns existence of a valid finite input, not a decision
procedure for existence of a derivation. -/
theorem derives_iff_exists_valid_tree (Γ : Context L) (φ : AlphaFormula L) :
    Derives Γ φ ↔ ∃ T : SequentTree L, T.root = (Γ, φ) ∧ T.Valid := by
  constructor
  · exact Derives.exists_valid_tree
  · rintro ⟨T, hT, hv⟩
    have h := hv.derives
    simpa only [hT] using h

end PolishSpaceBook.NamedFirstOrder
