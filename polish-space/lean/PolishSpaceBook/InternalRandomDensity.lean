module

public import PolishSpaceBook.CantorDensityRelations

@[expose] public section

/-! # Internally constructed density exceptions and random points

Only the cited cylinder density theorem is supplied as external measure
theory. The entire exception code is constructed from the original internal
Borel code, using Separation for the deviation relations and Replacement for
the nested label-graph families.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels CantorTreeMeasure
open Filter Topology
universe u

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence) (c : Code) (hc : c.val.labelGraph ∈ M)

include hM hinf hpair hunion hpower hsep hrep hchoice hc

/-- Internality of the whole exception code is derived from the original Borel input. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    Separation on $\omega\times(\omega\times\omega)$ collects each whole deviation-comparison relation, indexed
    by $(k,N,s)$. The union, complement, selected-leaf, and empty-leaf cases give a bounded description of every
    label in the nested Borel expressions above. The shared graph-collection construction puts the entire label
    graphs and the required sequences of label graphs in $M$. The internal Boolean constructors then give a code
    in $M$ for
    $$N_A=(A\cap E_1)\cup(A^c\cap E_0).$$
-/
theorem Code.densityException_internal : c.densityException.val.labelGraph ∈ M := by
  obtain ⟨D₀, hD₀, hs₀⟩ := exists_internal_densityRelation hM hinf hpair hunion hpower hsep hrep hchoice c hc false
  obtain ⟨D₁, hD₁, hs₁⟩ := exists_internal_densityRelation hM hinf hpair hunion hpower hsep hrep hchoice c hc true
  apply Code.densityException_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc D₀ D₁ hD₀ hD₁
  intro t
  cases t
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hs₀
  · simpa only [↓reduceIte] using hs₁

/-- Avoiding old null codes yields both density limits for every old Borel code. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  excerpt: |
    \begin{proposition*}[Lebesgue-point property] For every Borel $A$ coded in the ground model,
    $$
    r_G\in A\quad\Longrightarrow\quad
    \lim_{s\prefixOf r_G}\mu_s(A)=1,
    $$
    and
    $$
    r_G\notin A\quad\Longrightarrow\quad
    \lim_{s\prefixOf r_G}\mu_s(A)=0.
    $$
    \end{proposition*}
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    The cited cylinder density theorem makes this exceptional set null. Since $r_G$ avoids every null Borel
    set whose code belongs to $M$, it lies outside $N_A$. If $r_G\in A$, it consequently lies outside $E_1$, and its
    cylinder densities converge to one. If $r_G\notin A$, it lies outside $E_0$, and those densities converge to zero.
    \end{proof}
-/
theorem AvoidsNullCodes.density_limits_of_internal_code {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (hdensity : Code.CylinderDensityTheorem c.cantor) :
    (x ∈ c.cantor → Tendsto (densitySequence c.cantor x) atTop (𝓝 1)) ∧
    (x ∉ c.cantor → Tendsto (densitySequence c.cantor x) atTop (𝓝 0)) :=
  hx.density_limits c (Code.densityException_internal hM hinf hpair hunion hpower hsep hrep hchoice c hc) hdensity

end PolishSpaceBook.BorelExpression
