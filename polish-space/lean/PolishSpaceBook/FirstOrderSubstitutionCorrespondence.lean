module

public import PolishSpaceBook.FirstOrderLiteralSubstitution

@[expose] public section

/-!
# Simultaneous substitution under corresponding variable names

Fresh bound representatives turn the comparison into literal replacement.
The resulting correspondence is syntactic and therefore proves equality of
alpha-classes when the supplied relation on free names is equality.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v
variable {L : Language.{u,v}}

namespace Formula.NameRel

theorem transport {R : ℕ → ℕ → Prop} {φ ψ φ' ψ' : Formula L} (h : NameRel R φ ψ)
    (hφ : Alpha φ φ') (hψ : Alpha ψ ψ') : NameRel R φ' ψ' := by
  have hh := hφ.symm.nameRel.trans h (fun a b c hab hbc => by subst b; exact hbc)
  exact hh.trans hψ.nameRel (fun a b c hab hbc => by subst c; exact hab)

end Formula.NameRel
namespace AlphaFormula

/-- Comparison of representatives, independent of their bound-name choices. -/
def Corresponds (R : ℕ → ℕ → Prop) (φ ψ : AlphaFormula L) : Prop :=
  ∃ a b : Formula L, mk a = φ ∧ mk b = ψ ∧ Formula.NameRel R a b

theorem corresponds_mk (R : ℕ → ℕ → Prop) (φ ψ : Formula L) :
    Corresponds R (mk φ) (mk ψ) ↔ Formula.NameRel R φ ψ := by
  constructor
  · rintro ⟨a,b,ha,hb,h⟩
    exact h.transport (Quotient.exact ha) (Quotient.exact hb)
  · intro h; exact ⟨φ,ψ,rfl,rfl,h⟩

namespace Corresponds

theorem eq {φ ψ : AlphaFormula L} (h : Corresponds Eq φ ψ) : φ = ψ := by
  rcases h with ⟨a,b,rfl,rfl,h⟩
  exact Quotient.sound h.eq_alpha

theorem falsum (R : ℕ → ℕ → Prop) : Corresponds R (falsum : AlphaFormula L) falsum :=
  ⟨.falsum,.falsum,rfl,rfl,.falsum R⟩

theorem equal {R : ℕ → ℕ → Prop} {t t' r r' : L.Term ℕ}
    (h : TermRel R t t') (h' : TermRel R r r') : Corresponds R (equal t r) (equal t' r') :=
  ⟨.equal t r,.equal t' r',rfl,rfl,.equal h h'⟩

theorem rel {R : ℕ → ℕ → Prop} {n : ℕ} (P : L.Relations n) {ts us : Fin n → L.Term ℕ}
    (h : ∀ i, TermRel R (ts i) (us i)) : Corresponds R (rel P ts) (rel P us) :=
  ⟨.rel P ts,.rel P us,rfl,rfl,.rel P h⟩

theorem binary (c : Connective) {R : ℕ → ℕ → Prop} {φ φ' ψ ψ' : AlphaFormula L}
    (h : Corresponds R φ φ') (h' : Corresponds R ψ ψ') :
    Corresponds R (binary c φ ψ) (binary c φ' ψ') := by
  rcases h with ⟨a,b,rfl,rfl,h⟩
  rcases h' with ⟨c',d,rfl,rfl,h'⟩
  exact ⟨.binary c a c',.binary c b d,rfl,rfl,.binary c h h'⟩

theorem quant (q : Quantifier) {R : ℕ → ℕ → Prop} {x y : ℕ} {φ ψ : AlphaFormula L}
    (h : Corresponds (bindNames R x y) φ ψ) : Corresponds R (quant q x φ) (quant q y ψ) := by
  rcases h with ⟨a,b,rfl,rfl,h⟩
  exact ⟨.quant q x a,.quant q y b,rfl,rfl,.quant q h⟩

end Corresponds
end AlphaFormula

/-- Related replacements give related terms by induction on the common template. -/
theorem termRel_subst (t : L.Term ℕ) (σ τ : ℕ → L.Term ℕ) (R : ℕ → ℕ → Prop)
    (h : ∀ x ∈ t.varFinset, TermRel R (σ x) (τ x)) : TermRel R (t.subst σ) (t.subst τ) := by
  induction t with
  | var x => exact h x (by simp)
  | func f ts ih =>
    apply TermRel.func f
    intro i
    apply ih i
    intro x hx
    exact h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)

namespace Formula

/-- Fresh binders preserve comparison of the replacement terms beneath every quantifier. -/
theorem literalSubst_corresponds (φ : Formula L) (σ τ : ℕ → L.Term ℕ) (R : ℕ → ℕ → Prop)
    (h : ∀ x ∈ φ.fv, TermRel R (σ x) (τ x))
    (hσ : ∀ y ∈ φ.boundNames, σ y = .var y ∧ ∀ x, x ≠ y → y ∉ (σ x).varFinset)
    (hτ : ∀ y ∈ φ.boundNames, τ y = .var y ∧ ∀ x, x ≠ y → y ∉ (τ x).varFinset) :
    NameRel R (φ.literalSubst σ) (φ.literalSubst τ) := by
  induction φ generalizing R with
  | falsum => exact .falsum _
  | equal t r =>
    exact .equal (termRel_subst t σ τ R (fun x hx => h x (Finset.mem_union_left _ hx)))
      (termRel_subst r σ τ R (fun x hx => h x (Finset.mem_union_right _ hx)))
  | rel P ts =>
    exact .rel P (fun i => termRel_subst (ts i) σ τ R
      (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)))
  | binary c φ ψ ihφ ihψ =>
    apply NameRel.binary c
    · exact ihφ R (fun x hx => h x (Finset.mem_union_left _ hx))
        (fun y hy => hσ y (Finset.mem_union_left _ hy)) (fun y hy => hτ y (Finset.mem_union_left _ hy))
    · exact ihψ R (fun x hx => h x (Finset.mem_union_right _ hx))
        (fun y hy => hσ y (Finset.mem_union_right _ hy)) (fun y hy => hτ y (Finset.mem_union_right _ hy))
  | quant q y φ ih =>
    apply NameRel.quant q
    apply ih (bindNames R y y)
    · intro x hx
      by_cases hxy : x = y
      · subst x
        rw [(hσ y (Finset.mem_insert_self _ _)).1, (hτ y (Finset.mem_insert_self _ _)).1]
        exact .var (Or.inl ⟨rfl,rfl⟩)
      · apply (h x (Finset.mem_erase.mpr ⟨hxy,hx⟩)).congr
        intro a ha b hb hab
        exact Or.inr ⟨fun he => (hσ y (Finset.mem_insert_self _ _)).2 x hxy (he ▸ ha),
          fun he => (hτ y (Finset.mem_insert_self _ _)).2 x hxy (he ▸ hb), hab⟩
    · intro z hz; exact hσ z (Finset.mem_insert_of_mem hz)
    · intro z hz; exact hτ z (Finset.mem_insert_of_mem hz)

end Formula
namespace AlphaFormula

abbrev inputSubstitution {n : ℕ} (ts : Fin n → L.Term ℕ) (x : ℕ) : L.Term ℕ :=
  if h : x < n then ts ⟨x,h⟩ else .var x

theorem inputSubstitution_fresh {n : ℕ} (ts : Fin n → L.Term ℕ) (y : ℕ)
    (hy : y ∉ Finset.range n ∪ argumentVars ts) :
    inputSubstitution ts y = .var y ∧ ∀ x, x ≠ y → y ∉ (inputSubstitution ts x).varFinset := by
  have hn : ¬y < n := fun h => hy (Finset.mem_union_left _ (Finset.mem_range.mpr h))
  refine ⟨dite_eq_right hn, ?_⟩
  intro x hxy
  dsimp only [inputSubstitution]
  split_ifs with hx
  · intro h
    exact hy (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨x,hx⟩, Finset.mem_univ _, h⟩))
  · simpa only [Term.varFinset, Finset.mem_singleton] using Ne.symm hxy

/-- Instantiating one definition with corresponding arguments preserves the full name relation. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Let $R$ be any relation on names, and suppose $\FirstOrderNameCorrespondence{R}{t_i}{u_i}$ for every input position.
    Structural induction on the common representative gives
    $$\FirstOrderNameCorrespondence{R}
    {\varphi\subst{\vec{x}}{\vec{t}}}{\varphi\subst{\vec{x}}{\vec{u}}}.$$
    At a quantifier with bound name $y$, both replacements fix $y$, and no replacement of another name contains $y$.
    Consequently the compared terms remain related under $\FirstOrderBoundNames{R}{y}{y}$, as required for the body.
    Atoms and connectives follow componentwise. Comparison is unchanged by replacing either representative by an
    $\alpha$-equivalent one: compose with comparison under equality using the comparison lemma above.
-/
theorem simultaneous_corresponds {n : ℕ} (φ : AlphaFormula L) (ts us : Fin n → L.Term ℕ)
    (R : ℕ → ℕ → Prop) (hf : φ.fv ⊆ Finset.range n) (hargs : ∀ i, TermRel R (ts i) (us i)) :
    Corresponds R (φ.simultaneous ts) (φ.simultaneous us) := by
  let B := φ.substitutionBound ts
  let C := φ.substitutionBound us
  have hb := φ.substitutionBound_spec ts
  have hc := φ.substitutionBound_spec us
  obtain ⟨ψ, he, hψ⟩ := φ.exists_fresh_rep
    ((Finset.range n ∪ temporaryNames n B ∪ argumentVars ts) ∪
      (Finset.range n ∪ temporaryNames n C ∪ argumentVars us))
  have hb' : ∀ x ∈ ψ.fv, x < B := by
    intro x hx
    apply hb.2.1 x
    rw [← he]; exact hx
  have hc' : ∀ x ∈ ψ.fv, x < C := by
    intro x hx
    apply hc.2.1 x
    rw [← he]; exact hx
  have hp : Disjoint ψ.boundNames (Finset.range n ∪ temporaryNames n B ∪ argumentVars ts) ∧
      Disjoint ψ.boundNames (Finset.range n ∪ temporaryNames n C ∪ argumentVars us) :=
    Finset.disjoint_union_right.mp hψ
  change Corresponds R (φ.simultaneousAt ts B) (φ.simultaneousAt us C)
  rw [← he, simultaneousAt_mk_literal ψ ts B hb.1 hb' hb.2.2 hp.1,
    simultaneousAt_mk_literal ψ us C hc.1 hc' hc.2.2 hp.2]
  apply (corresponds_mk R _ _).mpr
  apply ψ.literalSubst_corresponds
  · intro x hx
    have hx' : x ∈ φ.fv := by rw [← he]; exact hx
    have hn := Finset.mem_range.mp (hf hx')
    simpa only [dite_eq_left hn] using hargs ⟨x,hn⟩
  · intro y hy
    apply inputSubstitution_fresh ts y
    intro hm
    apply Finset.disjoint_left.mp hp.1 hy
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
    · exact Finset.mem_union_right _ hm
  · intro y hy
    apply inputSubstitution_fresh us y
    intro hm
    apply Finset.disjoint_left.mp hp.2 hy
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
    · exact Finset.mem_union_right _ hm

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
