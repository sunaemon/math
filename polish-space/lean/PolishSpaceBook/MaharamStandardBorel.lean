module

public import PolishSpaceBook.MaharamInterval
public import PolishSpaceBook.MeasureAlgebraIsomorphism
public import PolishSpaceBook.PerfectSetsStandardBorelCoding
public import PolishSpaceBook.ConcreteCantorBaireModels

@[expose] public section

/-!
# Maharam's theorem for standard Borel probability spaces

Embed the standard Borel space into the unit interval, use its continuous
cdf and generalized inverse, and pull the inverse back along the embedding.
Two spaces are compared through the common Lebesgue model.
-/

noncomputable section
namespace PolishSpaceBook.MaharamStandardBorel
open Set Filter Function MeasureTheory unitInterval
open MaharamInterval

/-- The ternary Cantor embedding, with its range recorded inside the unit interval. -/
def cantorIntoInterval (x : cantor_space) : I :=
  ⟨middleThirdsCantorHomeomorph x, cantorSet_subset_unitInterval (middleThirdsCantorHomeomorph x).2⟩

lemma cantorIntoInterval_continuous : Continuous cantorIntoInterval :=
  (continuous_subtype_val.comp middleThirdsCantorHomeomorph.continuous).subtype_mk _

lemma cantorIntoInterval_injective : Injective cantorIntoInterval := by
  intro x y h
  apply middleThirdsCantorHomeomorph.injective
  exact Subtype.ext (congrArg (fun t : I => (t : ℝ)) h)

/-- The countable basis code followed by the ternary embedding gives a Borel image in `[0,1]`. -/
theorem exists_interval_embedding (X : Type*) [MeasurableSpace X] [StandardBorelSpace X] :
    ∃ θ : X → I, MeasurableEmbedding θ := by
  let := upgradeStandardBorel X
  let : PolishSpace cantor_space := cantor_space_polish
  obtain ⟨U, _, hU⟩ := exists_basisCode_measurableEmbedding (X := X)
  exact ⟨cantorIntoInterval ∘ basisCode U,
    (cantorIntoInterval_continuous.measurableEmbedding cantorIntoInterval_injective).comp hU⟩

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a general standard Borel $X$ with non-atomic $\mu$, choose a Borel isomorphism
    $$\theta:X\to B\IncludedIn[0,1]$$
    onto a Borel subset, using §{sec:standard-borel-classification}. Regard $\eta:=\theta_*\mu$ as a measure on
    $[0,1]$, so $\eta(\SetDifference{[0,1]}{B})=0$. It is again a non-atomic probability measure.
    Fix $x_0\in X$, and extend $\theta^{-1}$ to a Borel map $q:[0,1]\to X$ by setting $q(u)=x_0$ outside $B$.
    Then $q\circ\theta=\mathrm{id}$ everywhere and $\theta\circ q=\mathrm{id}$ $\eta$-almost everywhere.
    Apply the interval construction to $\eta$, and put
    $$f_X:=F\circ\theta,\qquad g_X:=q\circ G.$$
    The pushforward identities give
    $$\begin{aligned}
    (f_X)_*\mu&=F_*\eta=\lambda,\\
    (g_X)_*\lambda&=q_*\eta=\mu.
    \end{aligned}$$

    Moreover, $g_X(f_X(x))=x$ for $\mu$-almost every $x$: outside the inverse image of the exceptional set
    for $G\circ F$, this follows from $q\circ\theta=\mathrm{id}$. Since $G_*\lambda=\eta$ and $\eta(B)=1$,
    we have $G(u)\in B$ for $\lambda$-almost every $u$. At these points,
    $$f_X(g_X(u))=F(\theta(q(G(u))))=F(G(u))=u.$$
    Thus $f_X$ and $g_X$ preserve measure and are inverse almost everywhere.
-/
/-- Transport the interval cdf construction along a Borel embedding. The inverse
is extended measurably outside the image, which has zero pushed-forward mass. -/
def through_embedding (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (θ : X → I) (hθ : MeasurableEmbedding θ) : AEMeasureEquiv μ (volume : Measure I) := by
  letI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let η := μ.map θ
  haveI : IsProbabilityMeasure η := inferInstance
  haveI : NullSingletonClass η := ⟨fun t => by
    rw [show η = μ.map θ from rfl, hθ.map_apply]
    exact (subsingleton_singleton.preimage hθ.injective).measure_zero μ⟩
  let F := distribution η
  let G := quantile F
  have hF : MeasurePreserving F η volume := ⟨(distribution_continuous η).measurable, distribution_map η⟩
  have hG : MeasurePreserving G volume η :=
    ⟨(quantile_monotone (distribution_continuous η) (distribution_monotone η)
      (distribution_one η)).measurable, quantile_map_volume η⟩
  have hi : MeasurePreserving hθ.invFun η μ := by
    refine ⟨hθ.measurable_invFun, ?_⟩
    rw [show η = μ.map θ from rfl, Measure.map_map hθ.measurable_invFun hθ.measurable]
    have hid : hθ.invFun ∘ θ = id := funext hθ.leftInverse_invFun
    rw [hid, Measure.map_id]
  have hGF : ∀ᵐ t ∂η, G (F t) = t := by
    have hn : ∀ᵐ t ∂η, F t ∉ flatValues F := by
      apply ae_iff.mpr
      have hset : {t | ¬F t ∉ flatValues F} = distribution η ⁻¹' flatValues (distribution η) := by
        ext t
        simp only [not_not, F, mem_ofPred_eq, mem_preimage]
      rw [hset]
      exact badFibers_null η
    filter_upwards [hn] with t ht
    exact quantile_distribution η ht
  have hθi : ∀ᵐ t ∂η, θ (hθ.invFun t) = t := by
    apply hθ.ae_map_iff.mpr
    exact Eventually.of_forall fun x => congrArg θ (hθ.leftInverse_invFun x)
  refine ⟨F ∘ θ, hθ.invFun ∘ G, hF.comp (hθ.measurable.measurePreserving μ), hi.comp hG, ?_, ?_⟩
  · filter_upwards [(hθ.measurable.quasiMeasurePreserving μ).ae hGF] with x hx
    change hθ.invFun (G (F (θ x))) = x
    rw [hx]
    exact hθ.leftInverse_invFun x
  · filter_upwards [hG.quasiMeasurePreserving.ae hθi] with u hu
    change F (θ (hθ.invFun (G u))) = u
    rw [hu]
    exact distribution_quantile η u

/-- The unit interval is a common measure model for every nonatomic standard Borel probability. -/
def toInterval (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ] [StandardBorelSpace X] :
    AEMeasureEquiv μ (volume : Measure I) :=
  through_embedding μ _ (exists_interval_embedding X).choose_spec

/-- Use the two interval models in opposite directions. -/
def between (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν] [StandardBorelSpace X] [StandardBorelSpace Y] : AEMeasureEquiv μ ν :=
  (toInterval μ).trans (toInterval ν).symm

/-- Maharam's Borel-isomorphism witness, on conull Borel subsets of the original spaces. -/
theorem borel_isomorphism (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    [StandardBorelSpace X] [StandardBorelSpace Y] :
    ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
      ∃ e : A ≃ᵐ B, MeasurePreserving e (μ.comap Subtype.val) (ν.comap Subtype.val) :=
  (between μ ν).exists_conull_isomorphism

/-- Maharam's measure-algebra isomorphism preserves both Boolean operations and mass. -/
theorem measureAlgebra_isomorphism (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    [StandardBorelSpace X] [StandardBorelSpace Y] :
    ∃ e : MeasureAlgebra μ ≃o MeasureAlgebra ν, ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a :=
  ⟨MeasureAlgebra.ofAEEquiv (between μ ν), MeasureAlgebra.ofAEEquiv_mass (between μ ν)⟩

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Maharam, simplest form
-/
/-- The full book theorem: a measure-preserving Boolean algebra isomorphism,
with a measure-preserving Borel isomorphism off null sets as witness. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    They identify every non-atomic standard probability algebra with the fair-coin algebra, independently of
    its chosen Polish presentation.
-/
theorem maharam (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    [StandardBorelSpace X] [StandardBorelSpace Y] :
    ∃ E : MeasureAlgebra μ ≃o MeasureAlgebra ν,
      (∀ a, MeasureAlgebra.mass (E a) = MeasureAlgebra.mass a) ∧
      ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
        ∃ e : A ≃ᵐ B, MeasurePreserving e (μ.comap Subtype.val) (ν.comap Subtype.val) :=
  ⟨MeasureAlgebra.ofAEEquiv (between μ ν), MeasureAlgebra.ofAEEquiv_mass (between μ ν),
    borel_isomorphism μ ν⟩

end PolishSpaceBook.MaharamStandardBorel
