import BookAFK.ChartAmalgamation
import VaughtConjecture.Correspondence.Density.Structure
import VaughtConjecture.Correspondence.Density.DonorDensity
import VaughtConjecture.Stage.Countable

/-! # The published finite-chart class

This adapter is checked separately against the pinned AFK toolchain. It does not
change the dependencies of the main book project.
-/

namespace BookAFK

open FirstOrder FirstOrder.Language CategoryTheory VaughtConjecture Ordinal Cardinal
open FirstOrder.Language.Structure

def chartClass (β : Ordinal.{0}) : Set (Bundled.{0} templateLanguage.Structure) :=
  {M | IsTemplateChart β M.str}

theorem finite_chart {β : Ordinal.{0}} {M : Bundled.{0} templateLanguage.Structure}
    (hM : M ∈ chartClass β) : Finite M := by
  obtain ⟨n, _, e, _, _, _⟩ := hM
  exact Finite.of_injective e.symm e.symm.injective

theorem chart_jointEmbedding {β : Ordinal.{0}} (hβ : β < ω₁) :
    JointEmbedding (chartClass β) := by
  intro M hM N hN
  obtain ⟨P, I, hP, i, j⟩ := IsTemplateChart.jointEmbedding hβ hM hN
  exact ⟨⟨P, I⟩, hP, i, j⟩

theorem chart_amalgamation {β : Ordinal.{0}} (hβ : β < ω₁) :
    Amalgamation (chartClass β) := by
  intro M N P e f hM hN hP
  obtain ⟨Q, I, hQ, i, j, hij⟩ := IsTemplateChart.amalgamation hβ hM hN hP e f
  exact ⟨⟨Q, I⟩, i, j, hQ, hij⟩

def ChartIndex (β : Ordinal.{0}) :=
  {p : Σ n, StageType (blockStage β) n // 0 < p.1 ∧ p.2.IsLegalTemplate ω₁}

theorem chartIndex_nonempty {β : Ordinal.{0}} (hβ : β < ω₁) : Nonempty (ChartIndex β) := by
  let t := (Correspondence.isLegal_intervalScheme 1).toStageType (blockStage β)
  have ht : t.IsStronglyCodedLegal :=
    ⟨(Correspondence.isLegal_intervalScheme 1).isLegal_toStageType _,
      fun _ _ => Label.isStronglyCoded_bot _⟩
  exact ⟨⟨⟨1, t⟩, Nat.zero_lt_one,
    (StageType.isLegalTemplate_omega_one_iff_of_le (blockStage_lt_omega_one hβ).le).mpr ht⟩⟩

theorem chart_enumeration {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ C : ℕ → Bundled.{0} templateLanguage.Structure,
      (∀ n, C n ∈ chartClass β) ∧
      (∀ Q ∈ chartClass β, ∃ n, Nonempty (Q ≃[templateLanguage] C n)) := by
  classical
  let : Countable (Σ n, StageType (blockStage β) n) :=
    StageType.countable_sigma (countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hβ))
  let : Countable (ChartIndex β) := by unfold ChartIndex; infer_instance
  let : Nonempty (ChartIndex β) := chartIndex_nonempty hβ
  obtain ⟨f, hf⟩ := exists_surjective_nat (ChartIndex β)
  let C : ℕ → Bundled.{0} templateLanguage.Structure :=
    fun n => Bundled.of (f n).val.2.TemplateChart
  refine ⟨C, ?_, ?_⟩
  · intro n
    exact isTemplateChart_templateChart (f n).property.1 (f n).property.2
  · intro Q hQ
    obtain ⟨n, t, e, hn, ht, hr⟩ := hQ
    obtain ⟨j, hj⟩ := hf ⟨⟨n, t⟩, hn, ht⟩
    let E : t.TemplateChart ≃[templateLanguage] Q := {
      toEquiv := e
      map_fun' := fun g => Empty.elim g
      map_rel' := fun r xs => hr r xs }
    refine ⟨j, ?_⟩
    change Nonempty (Q ≃[templateLanguage] (f j).val.2.TemplateChart)
    rw [hj]
    exact ⟨E.symm⟩

/-- The actual AFK chart class has a countable universal extension structure.
Stage-class membership is a separate remaining assertion. -/
theorem exists_chart_limit {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ M : Bundled.{0} templateLanguage.Structure, Countable M ∧
      (∀ Q ∈ chartClass β, Nonempty (Q ↪[templateLanguage] M)) ∧
      (∀ A B : Bundled.{0} templateLanguage.Structure, A ∈ chartClass β → B ∈ chartClass β →
        ∀ (h : A ↪[templateLanguage] B) (e : A ↪[templateLanguage] M),
          ∃ g : B ↪[templateLanguage] M, g.comp h = e) ∧
      (∀ k (x : Fin k → M), ∃ (Q : Bundled.{0} templateLanguage.Structure)
        (_ : Q ∈ chartClass β) (i : Q ↪[templateLanguage] M) (y : Fin k → Q),
          ∀ t, i (y t) = x t) := by
  obtain ⟨C, hC, hcover⟩ := chart_enumeration hβ
  exact PolishSpaceBook.ChartAmalgamation.exists_countable_universal_extension
    (chart_amalgamation hβ) (chart_jointEmbedding hβ) C hC
    (fun _ hQ => finite_chart hQ) hcover

/-- Projection fixedness is invariant under a structure isomorphism. -/
theorem fixed_of_equiv (β : Ordinal.{0}) {M N : Type}
    [G : templateLanguage.Structure M] [H : templateLanguage.Structure N]
    (e : M ≃[templateLanguage] N) (hG : projectStructure β G = G) :
    projectStructure β H = H := by
  refine templateStructure_ext fun r xs => ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    have hp :
        RelMap (self := projectStructure β H) (TemplateSymbol.invariant c hk) xs ↔
        RelMap (self := projectStructure β G) (TemplateSymbol.invariant c hk) (e.symm ∘ xs) := by
      simp only [relMap_projectStructure_invariant]
      exact exists_congr fun d => and_congr_right fun _ => (e.symm.map_rel _ xs).symm
    rw [hG] at hp
    exact hp.trans (e.symm.map_rel _ xs)

/-- Every finite chart at stage β is fixed by that stage's projection. -/
theorem chart_fixed {β : Ordinal.{0}} (hβ : β < ω₁)
    {M : Bundled.{0} templateLanguage.Structure} (hM : M ∈ chartClass β) :
    projectStructure β M.str = M.str := by
  obtain ⟨n, t, e, _, _, hr⟩ := hM
  let E : t.TemplateChart ≃[templateLanguage] M := {
    toEquiv := e
    map_fun' := fun g => Empty.elim g
    map_rel' := fun r xs => hr r xs }
  have ht := ClassRealization.projectStructure_toStructure hβ t.faceClassRealization
  rw [StageType.toStructure_faceClassRealization] at ht
  exact fixed_of_equiv β E ht

def HasChartCover (β : Ordinal.{0}) (M : Type) [templateLanguage.Structure M] : Prop :=
  ∀ k (x : Fin k → M), ∃ (Q : Bundled.{0} templateLanguage.Structure)
    (_ : Q ∈ chartClass β) (i : Q ↪[templateLanguage] M) (y : Fin k → Q),
      ∀ t, i (y t) = x t

/-- Fixedness passes to a structure whose finite tuples lie in stage charts.
This uses the actual existential definition of projection on invariant symbols. -/
theorem fixed_of_chart_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M) :
    projectStructure β G = G := by
  refine templateStructure_ext fun r xs => ?_
  cases r with
  | closed hk => exact Iff.rfl
  | base c h0 hk => exact Iff.rfl
  | invariant c hk =>
    obtain ⟨Q, hQ, e, y, hy⟩ := hcover _ xs
    have he : e ∘ y = xs := funext hy
    have hr (d : LegalClass _) :
        RelMap (self := G) (TemplateSymbol.invariant d hk) xs ↔
        RelMap (self := Q.str) (TemplateSymbol.invariant d hk) y := by
      rw [← he]
      exact e.map_rel _ y
    rw [relMap_projectStructure_invariant]
    calc
      (∃ d, d.project β = c ∧ RelMap (self := G) (TemplateSymbol.invariant d hk) xs) ↔
          (∃ d, d.project β = c ∧ RelMap (self := Q.str) (TemplateSymbol.invariant d hk) y) :=
        exists_congr fun d => and_congr_right fun _ => hr d
      _ ↔ RelMap (self := projectStructure β Q.str) (TemplateSymbol.invariant c hk) y := Iff.rfl
      _ ↔ RelMap (self := Q.str) (TemplateSymbol.invariant c hk) y := by rw [chart_fixed hβ hQ]
      _ ↔ RelMap (self := G) (TemplateSymbol.invariant c hk) xs := (hr c).symm

/-- Refine a chart cover to canonical finite charts with their proved
compatibility, without assuming compatibility of the ambient structure. -/
theorem compatible_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [templateLanguage.Structure M] (hcover : HasChartCover β M)
    (k : ℕ) (x : Fin k → M) :
    ∃ (Q : Bundled.{0} templateLanguage.Structure), IsTemplateCompatible Q.str ∧
      ∃ (i : Q ↪[templateLanguage] M) (y : Fin k → Q), ∀ t, i (y t) = x t := by
  obtain ⟨Q, hQ, i, y, hy⟩ := hcover k x
  obtain ⟨n, t, e, _, ht, hr⟩ := hQ
  let E : t.TemplateChart ≃[templateLanguage] Q := {
    toEquiv := e
    map_fun' := fun g => Empty.elim g
    map_rel' := fun r xs => hr r xs }
  have ht' := (StageType.isLegalTemplate_omega_one_iff_of_le
    (blockStage_lt_omega_one hβ).le).mp ht
  refine ⟨Bundled.of t.TemplateChart, ht'.isTemplateCompatible_chart,
    i.comp E.toEmbedding, e.symm ∘ y, ?_⟩
  intro a
  change i (e (e.symm (y a))) = x a
  simpa only [e.apply_symm_apply] using hy a

/-- All diagram pairs pass from finite charts to their covered union.
In particular, no ambient compatibility hypothesis is used here. -/
theorem pairs_of_chart_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M) :
    Correspondence.SatisfiesPairs templateDiagramPairs M := by
  refine (satisfiesPairs_templateDiagramPairs_iff G).mpr ?_
  intro n hn c x hx k r j
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have he : e ∘ y = x := funext hy
  have hx' : RelMap (self := Q.str) (TemplateSymbol.invariant c hn) y := by
    apply (e.map_rel _ y).mp
    rwa [he]
  have hr := (satisfiesPairs_templateDiagramPairs_iff Q.str).mp hQ.satisfiesPairs hn c y hx' r j
  rw [← he]
  exact (e.map_rel r (y ∘ j)).trans hr

theorem injective_closed_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M)
    (hx : RelMap (L := templateLanguage) (TemplateSymbol.closed hn) x) : Function.Injective x := by
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have he : e ∘ y = x := funext hy
  have hx' : RelMap (self := Q.str) (TemplateSymbol.closed hn) y := by
    apply (e.map_rel _ y).mp
    rwa [he]
  rw [← he]
  exact e.injective.comp (hQ.isStructuredGeometry.isGeometry.injective hn y hx')

theorem closed_perm_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) (p : Equiv.Perm (Fin n)) :
    RelMap (L := templateLanguage) (TemplateSymbol.closed hn) x ↔ RelMap (L := templateLanguage) (TemplateSymbol.closed hn) (x ∘ p) := by
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have he : e ∘ y = x := funext hy
  rw [← he]
  exact (e.map_rel _ y).trans
    ((hQ.isStructuredGeometry.isGeometry.perm hn y p).trans (e.map_rel _ (y ∘ p)).symm)

theorem exists_closed_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) (hx : Function.Injective x) :
    ∃ (k : ℕ) (z : Fin (n + k) → M), z ∘ Fin.castAdd k = x ∧
      RelMap (L := templateLanguage) (TemplateSymbol.closed (Nat.lt_add_right k hn)) z := by
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have hyi : Function.Injective y := fun a b hab => hx (by rw [← hy a, ← hy b, hab])
  obtain ⟨k, z, hz, hclosed⟩ := hQ.isStructuredGeometry.isGeometry.exists_closed hn y hyi
  refine ⟨k, e ∘ z, ?_, (e.map_rel _ z).mpr hclosed⟩
  ext a
  change e (z (Fin.castAdd k a)) = x a
  rw [show z (Fin.castAdd k a) = y a from congrFun hz a]
  exact hy a

theorem compatible_cover_pair {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n m : ℕ} (x : Fin n → M) (y : Fin m → M) :
    ∃ (Q : Bundled.{0} templateLanguage.Structure), IsTemplateCompatible Q.str ∧
      ∃ (e : Q ↪[templateLanguage] M) (a : Fin n → Q) (b : Fin m → Q),
        e ∘ a = x ∧ e ∘ b = y := by
  obtain ⟨Q, hQ, e, z, hz⟩ := compatible_cover hβ hcover (n + m) (Fin.append x y)
  refine ⟨Q, hQ, e, z ∘ Fin.castAdd m, z ∘ Fin.natAdd n, ?_, ?_⟩
  · ext i
    exact (hz (Fin.castAdd m i)).trans (Fin.append_left x y i)
  · ext i
    exact (hz (Fin.natAdd n i)).trans (Fin.append_right x y i)

theorem closed_iff_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    RelMap (L := templateLanguage) (templateSignature.closed n hn) x ↔
      ∃ r : templateLanguage.Relations n, templateSignature.IsInvariant r ∧ RelMap r x := by
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have he : e ∘ y = x := funext hy
  rw [← he]
  exact (e.map_rel _ y).trans ((hQ.isStructuredGeometry.closed_iff hn y).trans
    (exists_congr fun r => and_congr_right fun _ => (e.map_rel r y).symm))

theorem exclusive_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n : ℕ} (r s : templateLanguage.Relations n) (hr : templateSignature.IsInvariant r)
    (hs : templateSignature.IsInvariant s) (hrs : r ≠ s) (x : Fin n → M)
    (hx : RelMap r x) : ¬ RelMap s x := by
  obtain ⟨Q, hQ, e, y, hy⟩ := compatible_cover hβ hcover n x
  have he : e ∘ y = x := funext hy
  rw [← he] at hx ⊢
  exact fun hsx => hQ.isStructuredGeometry.exclusive r s hr hs hrs y
    ((e.map_rel r y).mp hx) ((e.map_rel s y).mp hsx)

theorem determines_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n k : ℕ} (r : templateLanguage.Relations n) (s : templateLanguage.Relations k)
    (j : Fin k → Fin n) (hr : templateSignature.IsInvariant r) (x y : Fin n → M)
    (hx : RelMap r x) (hy : RelMap r y) : RelMap s (x ∘ j) ↔ RelMap s (y ∘ j) := by
  obtain ⟨Q, hQ, e, a, b, ha, hb⟩ := compatible_cover_pair hβ hcover x y
  rw [← ha] at hx
  rw [← hb] at hy
  have hd := hQ.isStructuredGeometry.determines r s j hr a b
    ((e.map_rel r a).mp hx) ((e.map_rel r b).mp hy)
  rw [← ha, ← hb]
  exact (e.map_rel s (a ∘ j)).trans (hd.trans (e.map_rel s (b ∘ j)).symm)

theorem closed_inter_of_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M)
    {n m k : ℕ} (hn : 0 < n) (hm : 0 < m) (hk : 0 < k)
    (x : Fin n → M) (y : Fin m → M) (z : Fin k → M)
    (hx : RelMap (L := templateLanguage) (TemplateSymbol.closed hn) x)
    (hy : RelMap (L := templateLanguage) (TemplateSymbol.closed hm) y)
    (hz : Function.Injective z) (hr : Set.range z = Set.range x ∩ Set.range y) :
    RelMap (L := templateLanguage) (TemplateSymbol.closed hk) z := by
  obtain ⟨Q, hQ, e, a, d, ha, hd⟩ := compatible_cover_pair hβ hcover x (Fin.append y z)
  let b := d ∘ Fin.castAdd k
  let c := d ∘ Fin.natAdd m
  have hb : e ∘ b = y := by
    ext i
    exact (congrFun hd (Fin.castAdd k i)).trans (Fin.append_left y z i)
  have hc : e ∘ c = z := by
    ext i
    exact (congrFun hd (Fin.natAdd m i)).trans (Fin.append_right y z i)
  have hp {l : ℕ} (v : Fin l → Q) : e ⁻¹' Set.range (e ∘ v) = Set.range v := by
    ext q
    simp only [Set.mem_preimage, Set.mem_range, Function.comp_apply, e.injective.eq_iff]
  have hr' := congrArg (Set.preimage e) hr
  rw [← ha, ← hb, ← hc, Set.preimage_inter, hp, hp, hp] at hr'
  have hz' : Function.Injective c := Function.Injective.of_comp (hc.symm ▸ hz)
  have hx' : RelMap (self := Q.str) (TemplateSymbol.closed hn) a := by
    apply (e.map_rel _ a).mp
    rwa [ha]
  have hy' : RelMap (self := Q.str) (TemplateSymbol.closed hm) b := by
    apply (e.map_rel _ b).mp
    rwa [hb]
  have hi := hQ.isStructuredGeometry.isGeometry.inter hn hm hk a b c hx' hy' hz' hr'
  have hi' := (e.map_rel (TemplateSymbol.closed hk) c).mpr hi
  rwa [hc] at hi'

/-- The full compatibility conditions hold in the covered limit. -/
theorem compatible_of_chart_cover {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hcover : HasChartCover β M) :
    IsTemplateCompatible G where
  isStructuredGeometry := {
    isGeometry := {
      injective := fun {_} => injective_closed_of_cover hβ hcover
      perm := fun {_} => closed_perm_of_cover hβ hcover
      exists_closed := fun {_} => exists_closed_of_cover hβ hcover
      inter := fun {_ _ _} => closed_inter_of_cover hβ hcover }
    closed_iff := fun {_} => closed_iff_of_cover hβ hcover
    exclusive := fun {_} => exclusive_of_cover hβ hcover
    determines := fun {_ _} => determines_of_cover hβ hcover }
  satisfiesPairs := pairs_of_chart_cover hβ hcover

theorem nonempty_chart {β : Ordinal.{0}} {Q : Bundled.{0} templateLanguage.Structure}
    (hQ : Q ∈ chartClass β) : Nonempty Q := by
  obtain ⟨n, _, e, hn, _, _⟩ := hQ
  exact ⟨e ⟨0, hn⟩⟩

theorem nonempty_of_chart_cover {β : Ordinal.{0}} {M : Type}
    [templateLanguage.Structure M] (hcover : HasChartCover β M) : Nonempty M := by
  obtain ⟨Q, hQ, e, _, _⟩ := hcover 0 Fin.elim0
  exact (nonempty_chart hQ).map e

/-- The constructed chart limit satisfies all stage-class conditions except
density, which must still be proved from its extension property. -/
theorem exists_compatible_chart_limit {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ M : Bundled.{0} templateLanguage.Structure, Countable M ∧ Nonempty M ∧
      IsTemplateCompatible M.str ∧ projectStructure β M.str = M.str ∧
      (∀ Q ∈ chartClass β, Nonempty (Q ↪[templateLanguage] M)) ∧
      (∀ A B : Bundled.{0} templateLanguage.Structure, A ∈ chartClass β → B ∈ chartClass β →
        ∀ (h : A ↪[templateLanguage] B) (e : A ↪[templateLanguage] M),
          ∃ g : B ↪[templateLanguage] M, g.comp h = e) := by
  obtain ⟨M, hc, hu, he, hcover⟩ := exists_chart_limit hβ
  exact ⟨M, hc, nonempty_of_chart_cover hcover, compatible_of_chart_cover hβ hcover,
    fixed_of_chart_cover hβ hcover, hu, he⟩

/-- Projecting a donor to the current stage preserves its raw truncation at
every lower cutoff, including successor ordinals. -/
theorem project_truncEquiv {β : Ordinal.{0}} (hβ : β < ω₁)
    {δ : Ordinal.{0}} (hδ : δ ≤ blockStage β) {n : ℕ}
    (c : TemplateClass ω₁ n) :
    (c.project (isSuccPrelimit_blockStage β)).TruncEquiv δ c := by
  induction c using Quotient.inductionOn with
  | h t =>
    rw [TemplateClass.project_toClass, TemplateClass.truncEquiv_toClass_iff]
    refine ⟨t.project (isSuccPrelimit_blockStage β), StageType.IsCellRenaming.refl _, rfl, ?_⟩
    intro i j hij
    have hij' : i = j := Fin.ext hij
    subst j
    change Label.reduce δ (Label.reduce ω₁ (Label.reduce (blockStage β) (t.label i))) =
      Label.reduce δ (t.label i)
    rw [Label.reduce_reduce_of_ge (blockStage_lt_omega_one hβ).le,
      Label.reduce_reduce_of_le hδ]

theorem globalClass_restrictFace {α : Ordinal.{0}} {n m : ℕ}
    (t : StageType α n) (f : Fin m ↪ Fin n) :
    t.globalClass.restrictFace f = (StageType.restrictFace f t).map StageType.globalClass := by
  rw [StageType.globalClass, TemplateClass.restrictFace_toClass, StageType.restrictFace_reduce,
    Option.map_map]
  rfl

/-- The invariant-class diagram reads exactly the relations of its finite chart. -/
theorem holds_globalClass {α : Ordinal.{0}} {n k : ℕ}
    (t : StageType α n) (r : TemplateSymbol k) (j : Fin k → Fin n) :
    t.globalClass.Holds r j ↔ t.Holds r j := by
  unfold TemplateClass.Holds StageType.Holds
  refine exists_congr fun hi => ?_
  rw [globalClass_restrictFace]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨q, hq, hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨s.globalClass, by rw [hs]; rfl, hr⟩

def invariant_chart_embedding {α : Ordinal.{0}} {n : ℕ} {M : Type}
    [G : templateLanguage.Structure M] (hG : IsTemplateCompatible G)
    {hn : 0 < n} {c : LegalClass n} {x : Fin n → M}
    (hx : RelMap (L := templateLanguage) (TemplateSymbol.invariant c hn) x)
    (t : StageType α n) (ht : t.globalClass = c.1) : t.TemplateChart ↪[templateLanguage] M where
  toFun := x
  inj' := hG.injective_of_relMap_invariant hx
  map_fun' f := Empty.elim f
  map_rel' r j := (hG.relMap_comp_iff hx r j).trans (by
    rw [← ht]
    exact holds_globalClass t r j)

/-- The chart extension property gives every density axiom below the stage. -/
theorem density_of_extension {β : Ordinal.{0}} (hβ : β < ω₁) {M : Type}
    [G : templateLanguage.Structure M] (hG : IsTemplateCompatible G)
    (hfix : projectStructure β G = G)
    (hext : ∀ A B : Bundled.{0} templateLanguage.Structure,
      A ∈ chartClass β → B ∈ chartClass β →
        ∀ (h : A ↪[templateLanguage] B) (e : A ↪[templateLanguage] M),
          ∃ g : B ↪[templateLanguage] M, g.comp h = e)
    {δ : Ordinal.{0}} (hδ : δ < blockStage β) : SatisfiesDensityAt δ G := by
  classical
  let hlam := isSuccPrelimit_blockStage β
  have hstage := (blockStage_lt_omega_one hβ).le
  refine (satisfiesDensityAt_iff δ G).mpr ?_
  intro n m hn t u hu x hx
  have htfix := hG.project_eq_of_relMap_invariant hfix hx
  obtain ⟨p, hp⟩ := Quotient.exists_rep u.1
  have hp' : p.toClass = u.1 := hp
  have hpLegal : p.IsStronglyCodedLegal := by
    have hh := u.2
    rw [← hp] at hh
    exact hh
  rw [← hp, TemplateClass.holds_toClass] at hu
  obtain ⟨hi, q, hq, hqt⟩ := hu
  let ca : Fin n ↪ Fin (n + m) := ⟨Fin.castAdd m, hi⟩
  have hq' : StageType.restrictFace ca p = some q := hq
  let D := p.reduce hlam
  let T := q.reduce hlam
  have hDLegal : D.IsStronglyCodedLegal := hpLegal
  have hqLegal : q.IsStronglyCodedLegal :=
    ⟨hpLegal.1.restrictFace ca hq', StageType.isStronglyCoded_of_restrictFace hq' hpLegal.2⟩
  have hTLegal : T.IsStronglyCodedLegal := hqLegal
  have hTD : StageType.restrictFace ca D = some T := by
    rw [StageType.restrictFace_reduce, hq', Option.map_some]
  have hqt' : q.toClass = t.1 := by
    change q.globalClass = t.1 at hqt
    simpa only [StageType.globalClass, StageType.reduce_self] using hqt
  have hTgc : T.globalClass = t.1 := by
    change (q.project hlam).toClass = t.1
    rw [← TemplateClass.project_toClass, hqt']
    exact congrArg Subtype.val htfix
  have hDgc : D.globalClass = (u.project β).1 := by
    change (p.project hlam).toClass = u.1.project hlam
    rw [← TemplateClass.project_toClass, hp']
  let A : Bundled.{0} templateLanguage.Structure := Bundled.of T.TemplateChart
  let B : Bundled.{0} templateLanguage.Structure := Bundled.of D.TemplateChart
  have hA : A ∈ chartClass β :=
    isTemplateChart_templateChart hn ((StageType.isLegalTemplate_omega_one_iff_of_le hstage).mpr hTLegal)
  have hB : B ∈ chartClass β :=
    isTemplateChart_templateChart (Nat.lt_add_right m hn)
      ((StageType.isLegalTemplate_omega_one_iff_of_le hstage).mpr hDLegal)
  let ab := D.templateChartEmbedding hTD (StageType.IsCellRenaming.refl T)
  let e := invariant_chart_embedding hG hx T hTgc
  obtain ⟨g, hg⟩ := hext A B hA hB ab e
  have hprefix : (g : Fin (n + m) → M) ∘ Fin.castAdd m = x :=
    funext fun a => DFunLike.congr_fun hg a
  have hfull : RelMap (self := G) (TemplateSymbol.invariant (u.project β) (Nat.lt_add_right m hn))
      (g : Fin (n + m) → M) := by
    have hd : D.Holds (TemplateSymbol.invariant (u.project β) (Nat.lt_add_right m hn)) id :=
      ⟨Function.injective_id, D, StageType.restrictFace_refl D, hDgc⟩
    exact (g.map_rel _ id).mpr hd
  refine ⟨(g : Fin (n + m) → M) ∘ Fin.natAdd n, u.project β,
    project_truncEquiv hβ hδ.le u.1, ?_⟩
  have happ : Fin.append ((g : Fin (n + m) → M) ∘ Fin.castAdd m)
      ((g : Fin (n + m) → M) ∘ Fin.natAdd n) = (g : Fin (n + m) → M) :=
    Fin.append_castAdd_natAdd
  rw [← hprefix, happ]
  exact hfull

/-- Lemma 4.33: a countable member of the published stage class, universal
for its finite charts and satisfying the full chart extension property. -/
theorem exists_stage_chart_limit {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ M : Bundled.{0} templateLanguage.Structure, Countable M ∧
      M.str ∈ templateStageClass M β ∧
      (∀ Q ∈ chartClass β, Nonempty (Q ↪[templateLanguage] M)) ∧
      (∀ A B : Bundled.{0} templateLanguage.Structure, A ∈ chartClass β → B ∈ chartClass β →
        ∀ (h : A ↪[templateLanguage] B) (e : A ↪[templateLanguage] M),
          ∃ g : B ↪[templateLanguage] M, g.comp h = e) := by
  obtain ⟨M, hc, hnon, hG, hfix, hu, he⟩ := exists_compatible_chart_limit hβ
  exact ⟨M, hc, ⟨hnon, hG, hfix, fun _ hδ => density_of_extension hβ hG hfix he hδ⟩, hu, he⟩

end BookAFK
