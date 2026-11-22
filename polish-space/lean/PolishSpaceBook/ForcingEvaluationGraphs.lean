module

public import PolishSpaceBook.ForcingPairing
public import PolishSpaceBook.ForcingCheckClosure
public import PolishSpaceBook.ForcingFormulas

@[expose] public section

/-! # Ordered-pair names and internal graphs of evaluation on ground sets of names -/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open FirstOrder Language ZFSet SetTheoryModels ForcingAtomic ForcingFormulas
universe u

/-- Label every name in D by every forcing condition. -/
lemma allConditionsName_isName {P D : ZFSet.{u}} (hD : ∀ σ ∈ D, IsName P σ) :
    IsName P (ZFSet.prod D P) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, p, _, he⟩ := ZFSet.mem_prod.mp hz
    exact ⟨σ, p, he⟩
  · intro σ p hp
    obtain ⟨hσ, hp⟩ := ZFSet.pair_mem_prod.mp hp
    exact ⟨hp, hD σ hσ⟩

lemma valuation_allConditionsName (P D : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (ZFSet.prod D P) = ZFSet.range (fun σ : D => valuation G σ.val) := by
  apply ZFSet.ext
  intro z
  rw [mem_valuation, ZFSet.mem_range]
  constructor
  · rintro ⟨σ, p, _, hp, he⟩
    exact ⟨⟨σ, (ZFSet.pair_mem_prod.mp hp).1⟩, he⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨p, hpG, hpP⟩ := hG
    exact ⟨σ.val, p, hpG, ZFSet.pair_mem_prod.mpr ⟨σ.property, hpP⟩, rfl⟩

/-- Kuratowski's ordered pair, built using the all-conditions unordered-pair names. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For names $\sigma,\tau$, define the unordered-pair and ordered-pair names by
    $$\begin{aligned}
    \ForcingUnorderedPairName{P}{\sigma}{\tau}&:=\{\sigma,\tau\}\times P,\\
    \ForcingOrderedPairName{P}{\sigma}{\tau}
     &:=\ForcingUnorderedPairName{P}
     {\ForcingUnorderedPairName{P}{\sigma}{\sigma}}
     {\ForcingUnorderedPairName{P}{\sigma}{\tau}}.
    \end{aligned}$$
-/
def orderedPairName (P σ τ : ZFSet.{u}) : ZFSet.{u} :=
  pairName P (pairName P σ σ) (pairName P σ τ)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Both are names.
-/
lemma orderedPairName_isName {P σ τ : ZFSet.{u}} (hσ : IsName P σ) (hτ : IsName P τ) :
    IsName P (orderedPairName P σ τ) :=
  pairName_isName (pairName_isName hσ hσ) (pairName_isName hσ hτ)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Whenever $\emptyset\ne G\IncludedIn P$, the valuation equation gives
    $$\begin{aligned}
    \ForcingUnorderedPairName{P}{\sigma}{\tau}^G&=\{\sigma^G,\tau^G\},\\
    \ForcingOrderedPairName{P}{\sigma}{\tau}^G&=\langle\sigma^G,\tau^G\rangle.
    \end{aligned}$$
    The second identity uses the Kuratowski definition of an ordered pair.
-/
lemma valuation_orderedPairName (P σ τ : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (orderedPairName P σ τ) = pair (valuation G σ) (valuation G τ) := by
  simp only [orderedPairName, valuation_pairName P _ _ G hG, pair, ZFSet.pair_eq_singleton]

/-- Evaluate a name while retaining the name itself as the input of the graph. -/
def evaluationEntry (P σ : ZFSet.{u}) : ZFSet.{u} := orderedPairName P (check P σ) σ

/-- The inputs are literal ground sets; they are check names in the first coordinate. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Define
    $$\ForcingEvaluationName{P}{D}:=
     \{\ForcingOrderedPairName{P}{\check\sigma}{\sigma}:\sigma\in D\}\times P.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    We must first show that this set belongs to $M$.
-/
def evaluationGraphName (P D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (ZFSet.range (fun σ : D => evaluationEntry P σ.val)) P

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For each $\sigma\in D$, exactly one such $\rho$ belongs to $M$.
    Replacement in $M$ therefore collects these values into a set in $M$, and product closure gives
    $\ForcingEvaluationName{P}{D}\in M$. Its first coordinates are names, so it is itself a name.
-/
lemma evaluationGraphName_isName {P D : ZFSet.{u}} (hD : ∀ σ ∈ D, IsName P σ) :
    IsName P (evaluationGraphName P D) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, p, _, he⟩ := ZFSet.mem_prod.mp hz
    exact ⟨σ, p, he⟩
  · intro ρ p hp
    obtain ⟨hρ, hpP⟩ := ZFSet.pair_mem_prod.mp hp
    obtain ⟨σ, rfl⟩ := ZFSet.mem_range.mp hρ
    exact ⟨hpP, orderedPairName_isName (check_isName P σ.val) (hD σ.val σ.property)⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The check-name identity and the ordered-pair valuation give
    $$\ForcingOrderedPairName{P}{\check\sigma}{\sigma}^G
     =\langle\sigma,\sigma^G\rangle.$$
    Every member of $\ForcingEvaluationName{P}{D}^G$ therefore belongs to $e_D$.
    Conversely, choose $p\in G$. For each $\sigma\in D$, the name of the displayed pair occurs with condition $p$,
    so that pair belongs to the value. Thus $\ForcingEvaluationName{P}{D}^G=e_D\in M[G]$.
    Using the check name in the first coordinate preserves the original input name rather than evaluating it.
-/
lemma valuation_evaluationGraphName (P D : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (evaluationGraphName P D) = functionGraph (fun σ : D => valuation G σ.val) := by
  apply ZFSet.ext
  intro z
  rw [mem_valuation, functionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨ρ, p, _, hp, he⟩
    obtain ⟨hρ, _⟩ := ZFSet.pair_mem_prod.mp hp
    obtain ⟨σ, rfl⟩ := ZFSet.mem_range.mp hρ
    refine ⟨σ, ?_⟩
    simpa only [evaluationEntry, valuation_orderedPairName P _ _ G hG, valuation_check P G hG] using he
  · rintro ⟨σ, rfl⟩
    obtain ⟨p, hpG, hpP⟩ := hG
    exact ⟨evaluationEntry P σ.val, p, hpG,
      ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_range.mpr ⟨σ, rfl⟩, hpP⟩,
      by simp only [evaluationEntry, valuation_orderedPairName P _ _ G ⟨p, hpG, hpP⟩,
        valuation_check P G ⟨p, hpG, hpP⟩]⟩

lemma pair_mem_evaluationGraph (D : ZFSet.{u}) (G : Set ZFSet.{u}) (a b : ZFSet.{u}) :
    pair a b ∈ functionGraph (fun σ : D => valuation G σ.val) ↔ a ∈ D ∧ valuation G a = b := by
  rw [mem_functionGraph_global]
  constructor
  · rintro ⟨σ, hσ, he⟩
    obtain ⟨rfl, hb⟩ := ZFSet.pair_inj.mp he
    exact ⟨hσ, hb.symm⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, by rw [hb]⟩

lemma evaluationGraph_isFunc (D : ZFSet.{u}) (G : Set ZFSet.{u}) :
    ZFSet.IsFunc D (ZFSet.range (fun σ : D => valuation G σ.val))
      (functionGraph (fun σ : D => valuation G σ.val)) := functionGraph_isFunc _

lemma evaluationGraph_surjective (D : ZFSet.{u}) (G : Set ZFSet.{u}) :
    ∀ b ∈ ZFSet.range (fun σ : D => valuation G σ.val),
      ∃ a ∈ D, pair a b ∈ functionGraph (fun σ : D => valuation G σ.val) := by
  intro b hb
  obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hb
  exact ⟨a.val, a.property, (pair_mem_evaluationGraph D G a.val _).mpr ⟨a.property, rfl⟩⟩

end PolishSpaceBook.ForcingNames

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingNames ForcingFormulas ForcingAtomic
universe u

/-- A first-order equality defining the specified unordered-pair name. -/
def pairNameEqFormula {n : ℕ} (P σ τ ρ : Fin n) : ForcingFormulas.Formula n :=
  (unorderedPairFormula (Fin.last n) σ.castSucc τ.castSucc ⊓
    productEqFormula (Fin.last n) P.castSucc ρ.castSucc).ex

lemma realize_pairNameEqFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (hpair : M ⊨ pairingSentence)
    {n : ℕ} (P σ τ ρ : Fin n) (xs : Fin n → M) :
    (pairNameEqFormula P σ τ ρ).Realize Empty.elim xs ↔
      (xs ρ).val = pairName (xs P).val (xs σ).val (xs τ).val := by
  have hu {k : ℕ} (p a b : Fin k) (ys : Fin k → M) :
      (unorderedPairFormula p a b).Realize Empty.elim ys ↔
        (ys p).val = ({(ys a).val, (ys b).val} : ZFSet.{u}) :=
    realize_unorderedPairFormula (M : ZFClass) (fun _ hx _ hy => hM.mem_trans hy hx) p a b ys
  simp only [pairNameEqFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    hu, realize_productEqFormula hM hpair, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨a, ha, he⟩
    exact he.trans (by rw [ha]; rfl)
  · intro he
    exact ⟨⟨{(xs σ).val, (xs τ).val}, unorderedPair_mem hM hpair (xs σ).property (xs τ).property⟩,
      rfl, he⟩

/-- The two constituent names are bound variables, not an assumed closure operation. -/
def orderedPairNameEqFormula {n : ℕ} (P σ τ ρ : Fin n) : ForcingFormulas.Formula n :=
  (pairNameEqFormula P.castSucc.castSucc σ.castSucc.castSucc σ.castSucc.castSucc (Fin.last n).castSucc ⊓
    pairNameEqFormula P.castSucc.castSucc σ.castSucc.castSucc τ.castSucc.castSucc (Fin.last (n + 1)) ⊓
    pairNameEqFormula P.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1)) ρ.castSucc.castSucc).ex.ex

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
include hM hpair hunion hpower hsep

lemma pairName_mem (P σ τ : M) : pairName P.val σ.val τ.val ∈ M :=
  prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (unorderedPair_mem hM hpair σ.property τ.property) P.property

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If $P,\sigma,\tau\in M$, Pairing and product closure put both names in $M$.
-/
lemma orderedPairName_mem (P σ τ : M) : orderedPairName P.val σ.val τ.val ∈ M := by
  exact pairName_mem hM hpair hunion hpower hsep P
    ⟨pairName P.val σ.val σ.val, pairName_mem hM hpair hunion hpower hsep P σ σ⟩
    ⟨pairName P.val σ.val τ.val, pairName_mem hM hpair hunion hpower hsep P σ τ⟩

lemma realize_orderedPairNameEqFormula {n : ℕ} (P σ τ ρ : Fin n) (xs : Fin n → M) :
    (orderedPairNameEqFormula P σ τ ρ).Realize Empty.elim xs ↔
      (xs ρ).val = orderedPairName (xs P).val (xs σ).val (xs τ).val := by
  simp only [orderedPairNameEqFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pairNameEqFormula hM hpair, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨s, t, ⟨hs, ht⟩, he⟩
    exact he.trans (by rw [hs, ht]; rfl)
  · intro he
    exact ⟨⟨_, pairName_mem hM hpair hunion hpower hsep (xs P) (xs σ) (xs σ)⟩,
      ⟨_, pairName_mem hM hpair hunion hpower hsep (xs P) (xs σ) (xs τ)⟩, ⟨rfl, rfl⟩, he⟩

theorem evaluationRange_mem_extension (P D : M) (hD : ∀ σ ∈ D.val, IsName P.val σ)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P.val) :
    ZFSet.range (fun σ : D.val => valuation G σ.val) ∈ extension P.val M G := by
  apply (mem_extension P.val M G _).mpr
  exact ⟨ZFSet.prod D.val P.val,
    prod_mem_of_separation hM hpair hunion hpower (hsep _) D.property P.property,
    allConditionsName_isName hD, valuation_allConditionsName P.val D.val G hG⟩

include hinf hrep

/-- Parameters P, input σ, output ρ; the check name κ is quantified. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $\kappa(P,\sigma,c)$ be the first-order formula defining $c=\check\sigma$ by the internal recursion
    in §{sec:forcing-names-valuation}. Define
    $$\begin{aligned}
    u(P,\sigma,\tau,\rho)\;:\equiv\;&\exists Q\,
     (Q=\{\sigma,\tau\}\land\rho=Q\times P),\\
    o(P,\sigma,\tau,\rho)\;:\equiv\;&\exists s\,\exists t\,
     \bigl(u(P,\sigma,\sigma,s)\\
     &{}\land u(P,\sigma,\tau,t)\land u(P,s,t,\rho)\bigr),\\
    \varepsilon(P,\sigma,\rho)\;:\equiv\;&\exists c\,
     (\kappa(P,\sigma,c)\land o(P,c,\sigma,\rho)).
    \end{aligned}$$
    The pair and product equalities abbreviate their previously constructed first-order formulas.
-/
def evaluationEntryFormula : ForcingFormulas.Formula 3 :=
  (reindex (recursiveValueFormula checkStepFormula) (Fin.snoc (Fin.snoc ![(0 : Fin 4)] 1) 3) ⊓
    orderedPairNameEqFormula (0 : Fin 4) 3 1 2).ex

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The closure lemmas and their interpretation identities show that, for $P,\sigma,\rho\in M$,
    $$M\models\varepsilon(P,\sigma,\rho)
     \quad\Longleftrightarrow\quad\rho=\ForcingOrderedPairName{P}{\check\sigma}{\sigma}.$$
-/
lemma realize_evaluationEntryFormula (P σ ρ : M) :
    evaluationEntryFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ![P] σ) ρ) ↔
      ρ.val = evaluationEntry P.val σ.val := by
  have he (κ : M) :
      (Fin.snoc (Fin.snoc (Fin.snoc ![P] σ) ρ) κ ∘
        Fin.snoc (Fin.snoc ![(0 : Fin 4)] 1) 3) = Fin.snoc (Fin.snoc ![P] σ) κ := by
    ext i
    fin_cases i <;> rfl
  have hc (κ : M) : (recursiveValueFormula checkStepFormula).Realize Empty.elim
      (Fin.snoc (Fin.snoc ![P] σ) κ) ↔ κ.val = check P.val σ.val :=
    realize_recursiveValueFormula_external hM hinf hpair hunion hpower hsep hrep checkStepFormula ![P]
      (checkStep P.val) (fun a g b => realize_checkStepFormula hM hpair hunion (hsep _) P a g b)
      (fun a g => checkStep_mem hM hpair hunion hpower hsep P a g)
      (check P.val) (check_step_equation P.val) σ κ
  simp only [evaluationEntryFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, he, hc, realize_orderedPairNameEqFormula hM hpair hunion hpower hsep]
  change (∃ κ : M, κ.val = check P.val σ.val ∧
    ρ.val = orderedPairName P.val κ.val σ.val) ↔ _
  constructor
  · rintro ⟨κ, hκ, he⟩
    exact he.trans (by rw [hκ]; rfl)
  · intro he
    exact ⟨⟨check P.val σ.val, check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep P σ⟩, rfl, he⟩

lemma evaluationEntry_mem (P σ : M) : evaluationEntry P.val σ.val ∈ M :=
  orderedPairName_mem hM hpair hunion hpower hsep P
    ⟨check P.val σ.val, check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep P σ⟩ σ

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For each $\sigma\in D$, exactly one such $\rho$ belongs to $M$.
    Replacement in $M$ therefore collects these values into a set in $M$, and product closure gives
    $\ForcingEvaluationName{P}{D}\in M$. Its first coordinates are names, so it is itself a name.
-/
lemma evaluationGraphName_mem (P D : M) : evaluationGraphName P.val D.val ∈ M := by
  let f : D.val → M := fun σ => ⟨evaluationEntry P.val σ.val,
    evaluationEntry_mem hM hinf hpair hunion hpower hsep hrep P ⟨σ.val, hM.mem_trans σ.property D.property⟩⟩
  have hf := replacement_image_mem hM evaluationEntryFormula (hrep _) ![P] D.property f (by
    intro σ ρ
    rw [realize_evaluationEntryFormula hM hinf hpair hunion hpower hsep hrep]
    change ρ.val = (f σ).val ↔ ρ = f σ
    exact Subtype.ext_iff.symm)
  exact prod_mem_of_separation hM hpair hunion hpower (hsep _) hf P.property

/-- The actual evaluation graph on a ground set of names belongs to the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To use the evaluation of names in an internal construction, its graph must belong to the extension.
    We first construct this graph on any ground-model set of names, then restrict it to obtain a surjection
    onto a given extension set. Neither construction uses Choice.
-/
theorem evaluationGraph_mem_extension (P D : M) (hD : ∀ σ ∈ D.val, IsName P.val σ)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P.val) :
    functionGraph (fun σ : D.val => valuation G σ.val) ∈ extension P.val M G := by
  apply (mem_extension P.val M G _).mpr
  exact ⟨evaluationGraphName P.val D.val,
    evaluationGraphName_mem hM hinf hpair hunion hpower hsep hrep P D,
    evaluationGraphName_isName hD, valuation_evaluationGraphName P.val D.val G hG⟩

/-- The graph, range, and ground domain belong to the same extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Evaluation graphs in extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Similarly, $D\times P\in M$ is a name and $(D\times P)^G=Y_D$, so $Y_D\in M[G]$.
    Check-name closure also gives $D\in M[G]$.
    The definition of $e_D$ shows that it is a function on $D$ with image exactly $Y_D$.
-/
theorem evaluation_graphs_in_extension (P D : M) (hD : ∀ σ ∈ D.val, IsName P.val σ)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P.val) :
    let Y := ZFSet.range (fun σ : D.val => valuation G σ.val)
    let e := functionGraph (fun σ : D.val => valuation G σ.val)
    e ∈ extension P.val M G ∧ Y ∈ extension P.val M G ∧ D.val ∈ extension P.val M G ∧
      ZFSet.IsFunc D.val Y e ∧ ∀ b ∈ Y, ∃ a ∈ D.val, pair a b ∈ e := by
  exact ⟨evaluationGraph_mem_extension hM hinf hpair hunion hpower hsep hrep P D hD G hG,
    evaluationRange_mem_extension hM hpair hunion hpower hsep P D hD G hG,
    ground_subset_extension_of_axioms hM hinf hpair hunion hpower hsep hrep P.property G hG D.property,
    evaluationGraph_isFunc D.val G, evaluationGraph_surjective D.val G⟩

end Model
end PolishSpaceBook.SetTheoryModels
