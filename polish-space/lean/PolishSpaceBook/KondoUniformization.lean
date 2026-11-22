module

public import PolishSpaceBook.KondoGraphComplexity
public import PolishSpaceBook.ZeroDimensionalPolishRefinement

@[expose] public section

/-! # Kondo uniformization from the cited scale theorem

Only existence of scales with their norm comparisons is supplied as an external
input. Alternating minima, convergence, graph complexity, and transfer through
the closed Baire presentation are deductions, proved in this module and its
three construction modules.
-/
namespace PolishSpaceBook.Kondo
noncomputable section
open Set MeasureTheory Topology

variable {X : Type} [TopologicalSpace X] [PolishSpace X]

/-- The cited coanalytic scale-existence theorem, restricted to the closed
Baire presentations used in the proof. It assumes no uniformizing graph. -/
def ScaleExistence (X : Type) [TopologicalSpace X] : Prop :=
  ∀ (F : Set baire_space), IsClosed F → ∀ A : Set (X × baire_space),
    CoanalyticSet A → (∀ p ∈ A, p.2 ∈ F) →
    ∃ s : Scale A F, Nonempty (Comparisons s)

theorem closed_baire_uniformization (scales : ScaleExistence X)
    {F : Set baire_space} (hF : IsClosed F) {A : Set (X × baire_space)}
    (hA : CoanalyticSet A) (hAF : ∀ p ∈ A, p.2 ∈ F) :
    ∃ G : Set (X × baire_space), CoanalyticSet G ∧ G ⊆ A ∧
      (∀ x y z, (x, y) ∈ G → (x, z) ∈ G → y = z) ∧ Prod.fst '' G = Prod.fst '' A := by
  obtain ⟨s, ⟨c⟩⟩ := scales F hF A hA hAF
  let G : Set (X × baire_space) := {p | Good s p.1 p.2}
  refine ⟨G, coanalytic_good c hA, fun _ hp => hp.1,
    fun _ _ _ hy hz => good_unique s hy hz, ?_⟩
  apply Subset.antisymm
  · exact image_mono fun _ hp => hp.1
  · rintro x ⟨⟨a, y⟩, hy, rfl⟩
    obtain ⟨z, hz⟩ := exists_good s hF hAF a ⟨y, hy⟩
    exact ⟨(a, z), hz, rfl⟩

/-- A continuous injection with closed range preserves coanalytic subsets:
the complement is the outside of the range together with the image of the
source complement. This also covers continuous bijections onto the target. -/
theorem coanalytic_image_closed_range {P Q : Type} [TopologicalSpace P] [PolishSpace P]
    [TopologicalSpace Q] [PolishSpace Q] {f : P → Q} (hf : Continuous f)
    (hinj : Function.Injective f) (hr : IsClosed (range f))
    {B : Set P} (hB : CoanalyticSet B) : CoanalyticSet (f '' B) := by
  have he : (f '' B)ᶜ = (range f)ᶜ ∪ f '' Bᶜ := by
    ext q
    constructor
    · intro hq
      by_cases hqr : q ∈ range f
      · obtain ⟨p, rfl⟩ := hqr
        exact Or.inr ⟨p, fun hp => hq ⟨p, hp, rfl⟩, rfl⟩
      · exact Or.inl hqr
    · rintro (hq | ⟨p, hp, rfl⟩)
      · exact fun ⟨p, _, he⟩ => hq ⟨p, he⟩
      · rintro ⟨p', hp', he⟩
        exact hp (hinj he ▸ hp')
  change AnalyticSet (f '' B)ᶜ
  rw [he]
  have hout : AnalyticSet (range f)ᶜ := by
    simpa using hr.isOpen_compl.analyticSet_image continuous_id
  exact analytic_union hout (hB.image_of_continuous hf)

/-- Kondo's conclusion, conditional only on the explicitly cited scale
existence theorem. The full local proof is the successive-minimum construction. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: statement
  kind: theorem
  title: Kondo
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] First use §{sec:closed-presentation-baire} to replace $Y$ by a closed subspace $F$ of
    $\BaireSpace$ through a Borel isomorphism. Analytic and coanalytic sets are preserved under Borel isomorphisms:
    analyticity is preserved under Borel images, and bijections commute with complements. Thus we may transfer both the
    relation and the eventual uniformizing graph between the two presentations. In this presentation the coordinates
    $y(n)$ are defined, and a coordinatewise limit remains in $F$ because $F$ is closed.
-/
theorem kondo_from_cited_scales {Y : Type} [TopologicalSpace Y] [PolishSpace Y]
    (scales : ScaleExistence X) {A : Set (X × Y)} (hA : CoanalyticSet A) :
    ∃ G : Set (X × Y), CoanalyticSet G ∧ G ⊆ A ∧
      (∀ x y z, (x, y) ∈ G → (x, z) ∈ G → y = z) ∧ Prod.fst '' G = Prod.fst '' A := by
  classical
  obtain ⟨F, hF, e, he, _⟩ := exists_continuous_closed_baire_presentation Y
  let : PolishSpace F := hF.polishSpace
  let toY : X × F → X × Y := fun p => (p.1, e p.2)
  let embed : X × F → X × baire_space := fun p => (p.1, p.2.val)
  have htoY : Continuous toY := continuous_fst.prodMk (he.comp continuous_snd)
  have hembed : Continuous embed := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hi : Function.Injective embed := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hh
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    exact Prod.ext hx (Subtype.ext hy)
  have hr : range embed = Prod.snd ⁻¹' F := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact y.property
    · intro hp
      exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
  let B : Set (X × F) := toY ⁻¹' A
  have hB : CoanalyticSet B := hA.preimage htoY
  have hAB : CoanalyticSet (embed '' B) := coanalytic_image_closed_range hembed hi
    (hr ▸ hF.preimage continuous_snd) hB
  obtain ⟨H, hH, hHB, hsingle, hdom⟩ := closed_baire_uniformization scales hF hAB (by
    rintro _ ⟨p, _, rfl⟩
    exact p.2.property)
  let K : Set (X × F) := embed ⁻¹' H
  have hK : CoanalyticSet K := hH.preimage hembed
  have hsurj : Function.Surjective toY := fun p => ⟨(p.1, e.symm p.2), by simp [toY]⟩
  have hinj : Function.Injective toY := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hh
    change (x, e y) = (x', e y') at hh
    apply Prod.ext
    · exact congrArg (fun p : X × Y => p.1) hh
    · exact e.injective (congrArg (fun p : X × Y => p.2) hh)
  refine ⟨toY '' K, coanalytic_image_closed_range htoY hinj
    (hsurj.range_eq ▸ isClosed_univ) hK, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', heq⟩ := hHB hp
    have hpp := hi heq
    exact hpp ▸ hp'
  · intro x y z hy hz
    obtain ⟨⟨a, b⟩, hb, hy⟩ := hy
    obtain ⟨⟨a', b'⟩, hb', hz⟩ := hz
    have ha : a = x := congrArg Prod.fst hy
    have ha' : a' = x := congrArg Prod.fst hz
    have hv := hsingle x b.val b'.val (by simpa [K, embed, ha] using hb)
      (by simpa [K, embed, ha'] using hb')
    have hbb : b = b' := Subtype.ext hv
    have hy' : e b = y := congrArg Prod.snd hy
    have hz' : e b' = z := congrArg Prod.snd hz
    exact hy'.symm.trans ((congrArg e hbb).trans hz')
  · apply Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hp
      obtain ⟨q', hq', heq⟩ := hHB hq
      have hqq := hi heq
      exact ⟨toY q, hqq ▸ hq', rfl⟩
    · rintro x ⟨⟨a, y⟩, hy, rfl⟩
      have hb : (a, e.symm y) ∈ B := by simpa [B, toY] using hy
      have hp : a ∈ Prod.fst '' (embed '' B) :=
        ⟨embed (a, e.symm y), ⟨(a, e.symm y), hb, rfl⟩, rfl⟩
      obtain ⟨⟨a', z⟩, hz, ha⟩ := hdom.symm ▸ hp
      have ha' : a' = a := ha
      obtain ⟨p, _, heq⟩ := hHB hz
      have hzF : z ∈ F := by
        have hval := congrArg Prod.snd heq
        change p.2.val = z at hval
        exact hval ▸ p.2.property
      refine ⟨(a, e ⟨z, hzF⟩), ⟨(a, ⟨z, hzF⟩), ?_, rfl⟩, rfl⟩
      simpa [K, embed, ha'] using hz

end
end PolishSpaceBook.Kondo
