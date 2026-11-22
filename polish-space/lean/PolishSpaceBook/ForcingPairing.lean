module

public import PolishSpaceBook.SetTheoryProducts

@[expose] public section

/-! # A ground-model name for a pair and preservation of the Pairing axiom -/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open FirstOrder Language ZFSet SetTheoryModels
universe u

/-- The all-conditions name whose valuation is the pair of two given valuations. -/
def pairName (P σ τ : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod {σ, τ} P

lemma pairName_isName {P σ τ : ZFSet.{u}} (hσ : IsName P σ) (hτ : IsName P τ) :
    IsName P (pairName P σ τ) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨π, _, p, _, hz⟩ := ZFSet.mem_prod.mp hz
    exact ⟨π, p, hz⟩
  · intro π p hp
    obtain ⟨hπ, hpP⟩ := ZFSet.pair_mem_prod.mp hp
    refine ⟨hpP, ?_⟩
    rcases ZFSet.mem_pair.mp hπ with rfl | rfl
    · exact hσ
    · exact hτ

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The valuation equation gives
    $$\begin{aligned}
    \rho^G&=\{\pi^G:\pi\in\{\sigma,\tau\},\;\exists p\in G\,(p\in P)\}\\
    &=\{\sigma^G,\tau^G\}=\{x,y\}.
    \end{aligned}$$
    The middle equality uses the nonemptiness of $G$ and $G\IncludedIn P$.
-/
lemma valuation_pairName (P σ τ : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (pairName P σ τ) = ({valuation G σ, valuation G τ} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  rw [mem_valuation, ZFSet.mem_pair]
  constructor
  · rintro ⟨π, p, _, hp, hz⟩
    obtain ⟨hπ, _⟩ := ZFSet.pair_mem_prod.mp hp
    rcases ZFSet.mem_pair.mp hπ with rfl | rfl
    · exact Or.inl hz.symm
    · exact Or.inr hz.symm
  · obtain ⟨p, hpG, hpP⟩ := hG
    rintro (hz | hz)
    · exact ⟨σ, p, hpG, ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_pair.mpr (Or.inl rfl), hpP⟩, hz.symm⟩
    · exact ⟨τ, p, hpG, ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_pair.mpr (Or.inr rfl), hpP⟩, hz.symm⟩

lemma pairName_mem_ground_of_separation {M P σ τ : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence productSeparationFormula)
    (hP : P ∈ M) (hσ : σ ∈ M) (hτ : τ ∈ M) : pairName P σ τ ∈ M :=
  prod_mem_of_separation hM hpair hunion hpower hsep (unorderedPair_mem hM hpair hσ hτ) hP

lemma pairName_mem_ground {M P σ τ : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hrep : M ⊨ replacementSentence (singletonSelector productSeparationFormula))
    (hP : P ∈ M) (hσ : σ ∈ M) (hτ : τ ∈ M) : pairName P σ τ ∈ M :=
  prod_mem hM hinf hpair hunion hpower hrep (unorderedPair_mem hM hpair hσ hτ) hP

/-- The Pairing axiom follows from the concrete pair name, without a truth-lemma assumption. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Thus the pair $\{x,y\}$ is the valuation of a name in $M$, so it belongs to $M[G]$.
    Since the extension uses actual membership, this set witnesses its internal Pairing axiom.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Pairing in the extension
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For $x,y\in M[G]$, choose names $\sigma,\tau\in M^P$ with $x=\sigma^G$ and $y=\tau^G$.
    Put
    $$\rho:=\{\sigma,\tau\}\times P.$$
    Pairing and the product construction in $M$ give $\rho\in M$.
    Every element of $\rho$ is an ordered pair whose first coordinate is one of the names $\sigma,\tau$ and whose
    second coordinate belongs to $P$. Hence $\rho$ is a $P$-name.
-/
theorem extension_models_pairing_of_separation {M P : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence productSeparationFormula)
    (hP : P ∈ M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) :
    extension P M G ⊨ pairingSentence := by
  apply (models_pairing_iff (extension P M G)).mpr
  intro x y
  obtain ⟨σ, hσM, hσ, hσx⟩ := (mem_extension P M G x.val).mp x.property
  obtain ⟨τ, hτM, hτ, hτy⟩ := (mem_extension P M G y.val).mp y.property
  have hp : ({x.val, y.val} : ZFSet.{u}) ∈ extension P M G := by
    apply (mem_extension P M G _).mpr
    refine ⟨pairName P σ τ, pairName_mem_ground_of_separation hM hpair hunion hpower hsep hP hσM hτM,
      pairName_isName hσ hτ, ?_⟩
    rw [valuation_pairName P σ τ G hG, hσx, hτy]
  refine ⟨⟨{x.val, y.val}, hp⟩, ?_⟩
  intro z
  simp only [ZFSet.mem_pair, Subtype.ext_iff]

theorem extension_models_pairing {M P : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hrep : M ⊨ replacementSentence (singletonSelector productSeparationFormula))
    (hP : P ∈ M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) :
    extension P M G ⊨ pairingSentence :=
  extension_models_pairing_of_separation hM hpair hunion hpower
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion
      productSeparationFormula hrep) hP G hG

end PolishSpaceBook.ForcingNames
