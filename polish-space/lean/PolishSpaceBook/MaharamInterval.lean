module

public import PolishSpaceBook.E0Nonsmooth
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section

/-!
# The distribution-function construction on the unit interval

The generalized inverse is the infimum of a closed upper level set. Its
adjunction with the distribution function gives the two pushforward identities.
Removing the countably many nontrivial fibers gives the Borel isomorphism.
-/

noncomputable section
namespace PolishSpaceBook.MaharamInterval

open Set MeasureTheory ProbabilityTheory Function unitInterval
open scoped ENNReal

/-- The leftmost point at which a monotone function reaches a given level. -/
def quantile (F : I → I) (u : I) : I := sInf {t | u ≤ F t}

lemma le_quantile_value {F : I → I} (hF : Continuous F) (h1 : F 1 = 1) (u : I) :
    u ≤ F (quantile F u) := by
  apply IsClosed.sInf_mem (s := {t | u ≤ F t})
  · exact ⟨1, by change u ≤ F 1; rw [h1]; exact le_top⟩
  · exact isClosed_le continuous_const hF

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For each $u\in[0,1]$, the set $C_u:=\{t\in[0,1]:u\le F(t)\}$ contains $1$ and is closed.
    It therefore contains its infimum, so $u\le F(G(u))$. Monotonicity of $F$ now gives
    $$G(u)\le t\quad\Longleftrightarrow\quad u\le F(t)
    \qquad(u,t\in[0,1]).$$
    In particular, $G$ is nondecreasing. By the intermediate value theorem, choose $t$ with $F(t)=u$.
    The equivalence gives $G(u)\le t$, whence
    $$u\le F(G(u))\le F(t)=u.$$
    Thus $F(G(u))=u$ for every $u$, including both endpoints. Both $F$ and $G$ are Borel maps.
-/
/-- The closed level set has a least point, including at levels zero and one. -/
lemma quantile_le_iff {F : I → I} (hF : Continuous F) (hmono : Monotone F)
    (h1 : F 1 = 1) (u t : I) : quantile F u ≤ t ↔ u ≤ F t := by
  constructor
  · intro h
    exact (le_quantile_value hF h1 u).trans (hmono h)
  · exact fun h => sInf_le h

lemma quantile_monotone {F : I → I} (hF : Continuous F) (hmono : Monotone F)
    (h1 : F 1 = 1) : Monotone (quantile F) := by
  intro u v huv
  exact (quantile_le_iff hF hmono h1 u _).mpr
    (huv.trans (le_quantile_value hF h1 v))

lemma quantile_rightInverse {F : I → I} (hF : Continuous F) (hmono : Monotone F)
    (h0 : F 0 = 0) (h1 : F 1 = 1) : RightInverse (quantile F) F := by
  intro u
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) 1 hF
    (show u ∈ Icc (F 0) (F 1) by rw [h0, h1]; exact ⟨bot_le, le_top⟩)
  apply le_antisymm _ (le_quantile_value hF h1 u)
  calc
    F (quantile F u) ≤ F t := hmono ((quantile_le_iff hF hmono h1 u t).mpr ht.ge)
    _ = u := ht

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    First suppose $X=[0,1]$ with a non-atomic Borel probability measure $\mu$. Its distribution function
    $$F(t):=\mu([0,t])$$
    is continuous and nondecreasing, with $F(0)=0$ and $F(1)=1$. Define the generalized inverse
    $$G(u):=\inf\{t\in[0,1]:F(t)\ge u\}.$$
-/
/-- The real-valued cdf, with its range recorded as the unit interval. -/
def distribution (μ : Measure I) (t : I) : I :=
  ⟨cdf (μ.map Subtype.val) t, cdf_nonneg _ _, cdf_le_one _ _⟩

variable (μ : Measure I) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [NullSingletonClass μ] in
lemma distribution_value (t : I) : (distribution μ t : ℝ) = μ.real (Iic t) := by
  change cdf (μ.map Subtype.val) t = _
  rw [unitInterval.cdf_eq_real]
  congr 1
  ext x
  simp only [mem_Icc, mem_Iic]
  exact and_iff_right x.2.1

omit [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma distribution_monotone : Monotone (distribution μ) := by
  intro s t h
  exact monotone_cdf _ h

lemma distribution_continuous : Continuous (distribution μ) := by
  have : IsProbabilityMeasure (μ.map (Subtype.val : I → ℝ)) :=
    inferInstance
  have : NullSingletonClass (μ.map (Subtype.val : I → ℝ)) := by
    constructor
    intro x
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
    exact (Set.subsingleton_singleton.preimage Subtype.val_injective).measure_zero μ
  exact Continuous.subtype_mk
    ((continuous_cdf_of_noAtoms (μ.map Subtype.val)).comp continuous_subtype_val) _

lemma distribution_zero : distribution μ 0 = 0 := by
  apply Subtype.ext
  rw [distribution_value]
  simp [measureReal_def, show Iic (0 : I) = {0} by ext x; simp]

omit [NullSingletonClass μ] in
lemma distribution_one : distribution μ 1 = 1 := by
  apply Subtype.ext
  rw [distribution_value]
  simp [show Iic (1 : I) = univ by ext x; simp; exact x.2.2]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The equivalence also identifies every initial-interval preimage:
    $$\{u:G(u)\le t\}=[0,F(t)],\qquad
    \lambda(\{u:G(u)\le t\})=F(t)=\mu([0,t]).$$
    Initial intervals determine Borel probability measures on the unit interval, so $G_*\lambda=\mu$.
    Pushing this identity forward by $F$ and using $F\circ G=\mathrm{id}$ gives
    $$F_*\mu=F_*(G_*\lambda)=(F\circ G)_*\lambda=\lambda.$$
-/
/-- The initial intervals determine the quantile pushforward. -/
theorem quantile_map_volume : volume.map (quantile (distribution μ)) = μ := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply
    (quantile_monotone (distribution_continuous μ) (distribution_monotone μ)
      (distribution_one μ)).measurable measurableSet_Iic]
  have hpre : quantile (distribution μ) ⁻¹' Iic t = Iic (distribution μ t) := by
    ext u
    exact quantile_le_iff (distribution_continuous μ) (distribution_monotone μ)
      (distribution_one μ) u t
  rw [hpre, unitInterval.volume_Iic, distribution_value, measureReal_def, ENNReal.ofReal_toReal]
  exact measure_ne_top μ _

/-- Applying the distribution function to its quantile recovers every level. -/
theorem distribution_quantile (u : I) : distribution μ (quantile (distribution μ) u) = u :=
  quantile_rightInverse (distribution_continuous μ) (distribution_monotone μ)
    (distribution_zero μ) (distribution_one μ) u

/-- Pushing forward first by the quantile and then by the cdf is the identity. -/
theorem distribution_map : μ.map (distribution μ) = volume := by
  conv_lhs => arg 2; rw [← quantile_map_volume μ]
  rw [Measure.map_map (distribution_continuous μ).measurable
    (quantile_monotone (distribution_continuous μ) (distribution_monotone μ)
      (distribution_one μ)).measurable]
  have hid : distribution μ ∘ quantile (distribution μ) = id :=
    funext (distribution_quantile μ)
  rw [hid, Measure.map_id]

/-- Levels at which the distribution function has a nontrivial interval fiber. -/
def flatValues (F : I → I) : Set I := {u | ∃ x y, x < y ∧ F x = u ∧ F y = u}

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $D$ be the set of values whose fibers under $F$ contain more than one point.
    If $x<y$ and $F(x)=F(y)=u$, choose a rational $q$ strictly between $x$ and $y$.
    Monotonicity gives $F(q)=u$, so
    $$D\IncludedIn F(\QQ\cap[0,1]).$$
-/
/-- Every nontrivial fiber contains a rational point; different fibers are disjoint. -/
lemma flatValues_countable {F : I → I} (hmono : Monotone F) : (flatValues F).Countable := by
  let R : Set I := Subtype.val ⁻¹' range (fun q : ℚ => (q : ℝ))
  have hR : R.Countable := (countable_range (fun q : ℚ => (q : ℝ))).preimage Subtype.val_injective
  apply (hR.image F).mono
  rintro u ⟨x, y, hxy, hx, hy⟩
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (show (x : ℝ) < y from hxy)
  let t : I := ⟨q, x.2.1.trans hxq.le, hqy.le.trans y.2.2⟩
  refine ⟨t, ⟨q, rfl⟩, ?_⟩
  exact le_antisymm ((hmono hqy.le).trans_eq hy) (hx.symm.trans_le (hmono hxq.le))

/-- Away from the flat fibers, the generalized inverse also recovers the point. -/
lemma quantile_distribution {t : I} (ht : distribution μ t ∉ flatValues (distribution μ)) :
    quantile (distribution μ) (distribution μ t) = t := by
  have hle := (quantile_le_iff (distribution_continuous μ) (distribution_monotone μ)
    (distribution_one μ) (distribution μ t) t).mpr le_rfl
  by_contra hne
  exact ht ⟨_, t, lt_of_le_of_ne hle hne, distribution_quantile μ _, rfl⟩

omit [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma flatValues_null : volume (flatValues (distribution μ)) = 0 :=
  (flatValues_countable (distribution_monotone μ)).measure_zero _

lemma badFibers_null : μ (distribution μ ⁻¹' flatValues (distribution μ)) = 0 := by
  rw [← Measure.map_apply (distribution_continuous μ).measurable
    (flatValues_countable (distribution_monotone μ)).measurableSet, distribution_map μ]
  exact flatValues_null μ

/-- The cdf and its generalized inverse restrict to mutually inverse Borel maps. -/
def conullEquiv (μ : Measure I) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ↥(distribution μ ⁻¹' (flatValues (distribution μ))ᶜ) ≃ᵐ
    ↥((flatValues (distribution μ))ᶜ) where
  toFun x := ⟨distribution μ x, x.2⟩
  invFun u := ⟨quantile (distribution μ) u, by
    change distribution μ (quantile (distribution μ) u) ∉ flatValues (distribution μ)
    rw [distribution_quantile]
    exact u.2⟩
  left_inv x := Subtype.ext (quantile_distribution μ x.2)
  right_inv u := Subtype.ext (distribution_quantile μ u)
  measurable_toFun := ((distribution_continuous μ).measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := ((quantile_monotone (distribution_continuous μ) (distribution_monotone μ)
    (distribution_one μ)).measurable.comp measurable_subtype_coe).subtype_mk

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Thus $D$ is countable, Borel, and Lebesgue null. By $F_*\mu=\lambda$, the Borel set
    $N:=F^{-1}(D)$ is $\mu$-null. If $t\notin N$, the equality $F(G(F(t)))=F(t)$ and the singleton-fiber condition
    imply $G(F(t))=t$. Conversely, $u\notin D$ implies $G(u)\notin N$ because $F(G(u))=u$.
    Consequently the restrictions
    $$\begin{aligned}
    F&:\SetDifference{[0,1]}{N}\longrightarrow\SetDifference{[0,1]}{D},\\
    G&:\SetDifference{[0,1]}{D}\longrightarrow\SetDifference{[0,1]}{N}
    \end{aligned}$$
    are inverse Borel maps. Their measure-preserving property follows by restricting the pushforward identities
    to these conull Borel subspaces.
-/
/-- Restricting to the two conull Borel subspaces preserves the pushforward identity. -/
theorem conullEquiv_measurePreserving : MeasurePreserving (conullEquiv μ)
    (μ.comap Subtype.val) (volume.comap Subtype.val) := by
  refine ⟨(conullEquiv μ).measurable, ?_⟩
  have hD := (flatValues_countable (distribution_monotone μ)).measurableSet.compl
  have hF := (distribution_continuous μ).measurable
  apply (MeasurableEmbedding.subtype_coe hD).map_injective
  rw [Measure.map_map measurable_subtype_coe (conullEquiv μ).measurable,
    map_comap_subtype_coe hD]
  change (μ.comap Subtype.val).map (distribution μ ∘ Subtype.val) = _
  rw [← Measure.map_map hF measurable_subtype_coe, map_comap_subtype_coe (hF hD),
    ← Measure.restrict_map hF hD, distribution_map μ]

/-- Every nonatomic Borel probability on the unit interval is Lebesgue measure
up to a measure-preserving Borel isomorphism of conull Borel subspaces. -/
theorem interval_isomorphism : ∃ (A B : Set I),
    MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ volume Bᶜ = 0 ∧
    ∃ e : A ≃ᵐ B, MeasurePreserving e (μ.comap Subtype.val) (volume.comap Subtype.val) := by
  refine ⟨distribution μ ⁻¹' (flatValues (distribution μ))ᶜ,
    (flatValues (distribution μ))ᶜ, ?_, ?_, ?_, ?_, conullEquiv μ,
    conullEquiv_measurePreserving μ⟩
  · exact (distribution_continuous μ).measurable
      (flatValues_countable (distribution_monotone μ)).measurableSet.compl
  · exact (flatValues_countable (distribution_monotone μ)).measurableSet.compl
  · simpa only [← preimage_compl, compl_compl] using badFibers_null μ
  · simpa only [compl_compl] using flatValues_null μ

end PolishSpaceBook.MaharamInterval
