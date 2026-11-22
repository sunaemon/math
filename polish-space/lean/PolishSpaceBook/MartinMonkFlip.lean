module

public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

@[expose] public section

/-! # A coordinate flip set cannot have the Baire property -/

noncomputable section
namespace PolishSpaceBook.MartinMonk
open Set Filter Topology

abbrev Cantor := ℕ → Bool

def flip (n : ℕ) (z : Cantor) : Cantor := fun k => if k = n then !(z k) else z k

@[simp] lemma flip_same (n : ℕ) (z : Cantor) : flip n z n = !(z n) := by simp [flip]
lemma flip_other {n k : ℕ} (h : k ≠ n) (z : Cantor) : flip n z k = z k := by simp [flip, h]
@[simp] lemma flip_flip (n : ℕ) (z : Cantor) : flip n (flip n z) = z := by
  funext k
  by_cases h : k = n <;> simp [flip, h]

lemma flip_continuous (n : ℕ) : Continuous (flip n) := by
  apply continuous_pi
  intro k
  by_cases h : k = n
  · simpa only [flip, h, ite_true, Function.comp_def] using
      (continuous_of_discreteTopology : Continuous Bool.not).comp (continuous_apply n)
  · simpa [flip, h] using (continuous_apply k : Continuous fun z : Cantor => z k)

def flipHomeomorph (n : ℕ) : Cantor ≃ₜ Cantor where
  toFun := flip n
  invFun := flip n
  left_inv := flip_flip n
  right_inv := flip_flip n
  continuous_toFun := flip_continuous n
  continuous_invFun := flip_continuous n

lemma flip_mem_cyl {s : List Bool} {n : ℕ} (hn : s.length ≤ n) {z : Cantor}
    (hz : z ∈ cyl s) : flip n z ∈ cyl s := by
  intro k hk
  rw [flip_other (by omega)]
  exact hz k hk

/-- A coordinate flip exchanges membership and nonmembership. -/
def IsFlipSet (D : Set Cantor) : Prop := ∀ n z, flip n z ∈ D ↔ z ∉ D

lemma flip_preimage {D : Set Cantor} (hD : IsFlipSet D) (n : ℕ) : (flip n) ⁻¹' D = Dᶜ := by
  ext z
  exact hD n z

lemma flip_not_meagre {D : Set Cantor} (hD : IsFlipSet D) : ¬ IsMeagre D := by
  let : PolishSpace Cantor := cantor_space_polish
  intro hm
  have hc : IsMeagre Dᶜ := by
    rw [← flip_preimage hD 0]
    exact hm.preimage_of_isOpenMap (flipHomeomorph 0).continuous (flipHomeomorph 0).isOpenMap
  have hall : IsMeagre (univ : Set Cantor) := by simpa using hm.union hc
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hall

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    No flip set has the Baire property. If $D$ were meager, then $h_n[D]=\SetDifference{\CantorSpace}{D}$ would also be
    meager, making the entire nonempty Baire space $\CantorSpace$ meager. Hence $D$ is non-meager.
    By the Baire property, there are an open set $U$ and a meager set $M$ with $\SymmetricDifference{D}{U}\IncludedIn M$.
    The set $U$ is nonempty, for otherwise $D\IncludedIn M$. Choose a nonempty basic cylinder $\cyl{s}\IncludedIn U$
    and $n\ge |s|$. Then $h_n$ preserves $\cyl{s}$, so
    $$
    \SetDifference{\cyl{s}}{D}\IncludedIn M,
    \qquad
    \cyl{s}\cap D\IncludedIn h_n[M].
    $$
    For the second inclusion, apply the first to $h_n(x)$ and use that $h_n$ is its own inverse and exchanges the two
    sides of $D$. Thus $\cyl{s}\IncludedIn M\cup h_n[M]$, making this nonempty open cylinder meager,
    contradicting the Baire category theorem. This proves that no strict descending sequence of Borel coarse Wadge degrees
    exists.
    \end{proof}
-/
/-- On a nonempty cylinder, a far coordinate flip would make both sides comeager. -/
theorem flip_not_baire {D : Set Cantor} (hD : IsFlipSet D) : ¬ BaireMeasurableSet D := by
  let : PolishSpace Cantor := cantor_space_polish
  intro hB
  obtain ⟨U, hU, heq⟩ := hB.residualEq_isOpen
  have hUn : U.Nonempty := by
    by_contra hn
    have hu : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hm : IsMeagre D := by
      change ∀ᶠ x in residual Cantor, x ∉ D
      filter_upwards [heq] with x hx
      intro hxD
      have hxU : x ∈ U := hx.mp hxD
      rw [hu] at hxU
      exact hxU
    exact flip_not_meagre hD hm
  obtain ⟨z, hz⟩ := hUn
  obtain ⟨s, hzs, hsU⟩ := exists_cyl_subset_of_mem_open hz hU
  have hflip : ∀ᶠ x in residual Cantor, (flip s.length x ∈ D) = (flip s.length x ∈ U) :=
    (tendsto_residual_of_isOpenMap (flipHomeomorph s.length).continuous
      (flipHomeomorph s.length).isOpenMap).eventually heq
  have hdense : Dense {x | (x ∈ D) = (x ∈ U) ∧
      (flip s.length x ∈ D) = (flip s.length x ∈ U)} :=
    dense_of_mem_residual (heq.and hflip)
  obtain ⟨x, hxs, hx, hfx⟩ := hdense.inter_open_nonempty (cyl s) (isOpen_cyl s) ⟨z, hzs⟩
  have hxD : x ∈ D := hx.mpr (hsU hxs)
  have hfxD : flip s.length x ∈ D := hfx.mpr (hsU (flip_mem_cyl le_rfl hxs))
  exact (hD s.length x).mp hfxD hxD

end PolishSpaceBook.MartinMonk
