module

public import PolishSpaceBook.LambdaRealizabilityCurrying

@[expose] public section

/-! # Uncurrying by application of a relation's numerical data -/
namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER
universe u

/-- Application retains a realizer of the chosen relation, but does not encode that relation. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Suppose $a\in F(z,R)$ and $b\in R(x,y)$. Strictness of $F$ gives extents for $z,R$.
    Extract the data for $R$ and apply its strictness program to $b$ to obtain extents for $x,y$.
    This proves strictness of the application relation. For extensionality, transport $a$ along $z\sim_Z z'$ using
    $F$, keeping $R$ fixed, and transport $b$ along $x\sim_X x'$ and $y\sim_Y y'$ using the data for $R$.
    Pair the two outputs. For single-valuedness, two inputs may use different relations $R,S$.
    Single-valuedness of $F$ gives $R\sim S$; convert the $S(x,y')$ realizer to $R(x,y')$, then use single-valuedness
    from the data for $R$.
    
    For totality, from extents for $z,x$ first compute $a\in F(z,R)$ for some $R$ by totality of $F$.
    Strictness of $F$ supplies data for $R$, whose totality program gives $b\in R(x,y)$ for some $y$.
    Return $\NatPair{a}{b}$. Neither $R$ nor $y$ has to be computed as a representative.
    All programs are uniform over the semantic witnesses, so existential elimination preserves these trackers.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability application relation}{Application relation}]
-/
def uncurryRelation {Z X Y : RealizerPER.{u}} (F : FunctionalRelation Z (functionSpace X Y)) :
    FunctionalRelation (product Z X) Y where
  val p y := {a | ∃ R, a.unpair.1 ∈ F.val p.1 R ∧ a.unpair.2 ∈ R p.2 y}
  strict := by
    let Γ : ((Z.Carrier × X.Carrier) × Y.Carrier) × RawFunction X Y → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1.1 p.2) (fun p => p.2 p.1.1.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hf : Reduces Γ (fun p => F.val p.1.1.1 p.2) := reduces_and_left _ _
    have hs := data_strict_of (extent_data_of (F.strict_right_of hf)) (reduces_and_right _ _)
    exact reduces_and_intro
      (reduces_and_intro (F.strict_left_of hf) (reduces_trans hs (reduces_and_left _ _)))
      (reduces_trans hs (reduces_and_right _ _))
  extensional := by
    let Γ : ((Z.Carrier × X.Carrier) × (Z.Carrier × X.Carrier) × Y.Carrier × Y.Carrier) ×
        RawFunction X Y → Set ℕ :=
      realizabilityAnd (realizabilityAnd
        (fun p => (product Z X).rel p.1.1 p.1.2.1)
        (realizabilityAnd (fun p => F.val p.1.1.1 p.2) (fun p => p.2 p.1.1.2 p.1.2.2.1)))
        (fun p => Y.rel p.1.2.2.1 p.1.2.2.2)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨⟨he, R, hf, hr⟩, hy⟩
      exact ⟨R, ⟨he, hf, hr⟩, hy⟩
    · have hf : Reduces Γ (fun p => F.val p.1.1.1 p.2) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_left _ _)
      have he := F.strict_right_of hf
      have hz : Reduces Γ (fun p => Z.rel p.1.1.1 p.1.2.1.1) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_left _ _)
      have hx : Reduces Γ (fun p => X.rel p.1.1.2 p.1.2.1.2) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_right _ _)
      have hr : Reduces Γ (fun p => p.2 p.1.1.2 p.1.2.2.1) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_right _ _)
      apply reduces_trans (reduces_and_intro (F.ext_of hz hf he)
        (data_ext_of (extent_data_of he) hx hr (reduces_and_right _ _)))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩
  single := by
    let Γ : ((Z.Carrier × X.Carrier) × Y.Carrier × Y.Carrier) ×
        (RawFunction X Y × RawFunction X Y) → Set ℕ :=
      realizabilityAnd
        (realizabilityAnd (fun p => F.val p.1.1.1 p.2.1) (fun p => p.2.1 p.1.1.2 p.1.2.1))
        (realizabilityAnd (fun p => F.val p.1.1.1 p.2.2) (fun p => p.2.2 p.1.1.2 p.1.2.2))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨⟨R, hf, hr⟩, ⟨S, hg, hs⟩⟩
      exact ⟨(R,S), ⟨hf,hr⟩, hg,hs⟩
    · have hf : Reduces Γ (fun p => F.val p.1.1.1 p.2.1) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
      have hg : Reduces Γ (fun p => F.val p.1.1.1 p.2.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      have hs : Reduces Γ (fun p => p.2.2 p.1.1.2 p.1.2.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
      have hr' := functionEquality_apply (F.single_of hg hf) hs
      exact data_single_of (extent_data_of (F.strict_right_of hf))
        (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) hr'
  total := by
    have ht := reduces_trans (reduces_and_left (fun p : Z.Carrier × X.Carrier => Z.extent p.1)
      (fun p => X.extent p.2)) (reindex_reduces Prod.fst F.total)
    apply reduces_trans (reduces_and_intro ht (reduces_and_right _ _))
    let Γ : (Z.Carrier × X.Carrier) × RawFunction X Y → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => X.extent p.1.2)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨⟨R,hf⟩,hx⟩
      exact ⟨R,hf,hx⟩
    · have hf : Reduces Γ (fun p => F.val p.1.1 p.2) := reduces_and_left _ _
      have ht' := data_total_of (extent_data_of (F.strict_right_of hf)) (reduces_and_right _ _)
      apply reduces_trans (reduces_and_intro hf ht')
      exact reduces_of_subset fun p _ ⟨hf',y,hy⟩ => ⟨y,p.2,hf',hy⟩

/-- Evaluation after currying recovers the original relation. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First, a realizer of $\UncurriedRelation{\CurriedRelation{H}}((z,x),y)$ supplies some $R$, a realizer of
    $R_z\sim R$, and a realizer of $R(x,y)$. Applying the reverse conversion gives a realizer of
    $R_z(x,y)=H((z,x),y)$. The two relations are functional, so this inclusion proves
    $$\UncurriedRelation{\CurriedRelation{H}}\equiv H.$$
-/
theorem uncurry_curry {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y) :
    (uncurryRelation (curryRelation H)).Equivalent H := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : ((Z.Carrier × X.Carrier) × Y.Carrier) × RawFunction X Y → Set ℕ :=
    realizabilityAnd (fun p => (curryRelation H).val p.1.1.1 p.2) (fun p => p.2 p.1.1.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have he : Reduces Γ (fun p => (functionSpace X Y).rel (functionSlice H p.1.1.1) p.2) :=
    reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
  exact functionEquality_apply (X := X) (Y := Y) ((functionSpace X Y).symm_of he) (reduces_and_right _ _)

/-- Uncurrying respects the quotient by uniform realizability equivalence. -/
theorem uncurry_mono {Z X Y : RealizerPER.{u}} {F G : FunctionalRelation Z (functionSpace X Y)}
    (h : F.LE G) : (uncurryRelation F).LE (uncurryRelation G) := by
  let Γ : ((Z.Carrier × X.Carrier) × Y.Carrier) × RawFunction X Y → Set ℕ :=
    realizabilityAnd (fun p => F.val p.1.1.1 p.2) (fun p => p.2 p.1.1.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hf : Reduces Γ (fun p => F.val p.1.1.1 p.2) := reduces_and_left _ _
  have hg : Reduces Γ (fun p => G.val p.1.1.1 p.2) :=
    reduces_trans hf (reindex_reduces (fun p : ((Z.Carrier × X.Carrier) × Y.Carrier) × RawFunction X Y => (p.1.1.1,p.2)) h)
  apply reduces_trans (reduces_and_intro hg (reduces_and_right _ _))
  exact reduces_of_subset fun p _ h => ⟨p.2,h⟩

/-- The slice of an uncurried arrow is uniformly equal to every value of that arrow. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Conversely, fix $a\in F(z,R)$ and put $S_z(x,y):=\UncurriedRelation{F}((z,x),y)$.
    Strictness of $F$ gives data for $R$ and an extent for $z$; uniform currying applied to
    $\UncurriedRelation{F}$ gives data for $S_z$.
    The program $b\mapsto\NatPair{a}{b}$ sends every $R(x,y)$ into $S_z(x,y)$.
    For the reverse direction, an input in $S_z(x,y)$ has the form $\NatPair{c}{b}$ with
    $c\in F(z,T)$ and $b\in T(x,y)$ for some $T$.
    Single-valuedness of $F$ applied to $c,a$ yields $T\sim R$; its forward conversion sends $b$ into $R(x,y)$.
    Abstracting $a$ computes both conversion indices, uniformly in $x,y,T$.
    Together with the two data tuples they realize $S_z\sim R$. Pair with the extent of $z$ to obtain
    $\CurriedRelation{\UncurriedRelation{F}}(z,R)$. Again one inclusion suffices, giving
    $$F\equiv\CurriedRelation{\UncurriedRelation{F}}.$$
-/
theorem uncurry_slice_equality {Z X Y : RealizerPER.{u}}
    (F : FunctionalRelation Z (functionSpace X Y)) :
    Reduces (fun p : Z.Carrier × RawFunction X Y => F.val p.1 p.2)
      (fun p => (functionSpace X Y).rel (functionSlice (uncurryRelation F) p.1) p.2) := by
  let Γ : Z.Carrier × RawFunction X Y → Set ℕ := fun p => F.val p.1 p.2
  have hf : Reduces Γ (fun p => F.val p.1 p.2) := reduces_refl _
  have hd : Reduces Γ (fun p => functionData (functionSlice (uncurryRelation F) p.1)) :=
    reduces_trans (F.strict_left_of hf) (reindex_reduces Prod.fst (functionSlice_data (uncurryRelation F)))
  change Reduces Γ (realizabilityAnd
    (realizabilityAnd (fun p => functionData (functionSlice (uncurryRelation F) p.1))
      (fun p => functionData p.2))
    (realizabilityAnd (fun p => relationEntailment (functionSlice (uncurryRelation F) p.1) p.2)
      (fun p => relationEntailment p.2 (functionSlice (uncurryRelation F) p.1))))
  apply reduces_and_intro (reduces_and_intro hd (extent_data_of (F.strict_right_of hf)))
  apply reduces_and_intro
  · apply uniformImp_intro
    let Δ : ((Z.Carrier × RawFunction X Y) × (X.Carrier × Y.Carrier)) × RawFunction X Y → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1.1 p.1.1.2)
        (realizabilityAnd (fun p => F.val p.1.1.1 p.2) (fun p => p.2 p.1.2.1 p.1.2.2))
    apply reduces_cover (θ := Δ)
    · rintro p a ⟨hf, S, hg, hs⟩
      exact ⟨S,hf,hg,hs⟩
    · have hf' : Reduces Δ (fun p => F.val p.1.1.1 p.1.1.2) := reduces_and_left _ _
      have hg : Reduces Δ (fun p => F.val p.1.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      exact functionEquality_apply (F.single_of hg hf')
        (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  · apply uniformImp_intro
    exact reduces_of_subset fun p _ h => ⟨p.1.2,h⟩

/-- Every arrow into the function object is recovered by currying its application relation. -/
theorem curry_uncurry {Z X Y : RealizerPER.{u}} (F : FunctionalRelation Z (functionSpace X Y)) :
    F.Equivalent (curryRelation (uncurryRelation F)) := by
  apply FunctionalRelation.equivalent_of_le
  exact reduces_and_intro (F.strict_left_of (reduces_refl _)) (uncurry_slice_equality F)

/-- A uniform equivalence of relations gives a uniform equality of all their slices. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    If $H\equiv K$, their fixed conversion programs also convert the slices at every $z$.
    Pairing these indices with the slice data computed from $E_Z(z)$ gives $R_z^H\sim R_z^K$ uniformly.
    Transitivity then converts the two graph relations, so currying descends to arrows.
    Together with the preceding lemma, the two identities give inverse bijections
    $$\HomSet{\EffCat}{Z\times X}{Y}\ \cong
      \HomSet{\EffCat}{Z}{\RealizabilityFunctionSpace{X}{Y}}.$$
    The inverse sends $f$ to $\evalMap\circ(f\times\mathrm{id}_X)$, proving existence and uniqueness.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability application relation}{Application relation}]
-/
theorem functionSlice_congr {Z X Y : RealizerPER.{u}}
    {H K : FunctionalRelation (product Z X) Y} (h : H.Equivalent K) :
    Reduces Z.extent (fun z => (functionSpace X Y).rel (functionSlice H z) (functionSlice K z)) := by
  change Reduces Z.extent (realizabilityAnd
    (realizabilityAnd (fun z => functionData (functionSlice H z)) (fun z => functionData (functionSlice K z)))
    (realizabilityAnd (fun z => relationEntailment (functionSlice H z) (functionSlice K z))
      (fun z => relationEntailment (functionSlice K z) (functionSlice H z))))
  apply reduces_and_intro (reduces_and_intro (functionSlice_data H) (functionSlice_data K))
  apply reduces_and_intro
  · apply uniformImp_intro
    exact reduces_trans (reduces_and_right _ _)
      (reindex_reduces (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => ((p.1,p.2.1),p.2.2)) h.1)
  · apply uniformImp_intro
    exact reduces_trans (reduces_and_right _ _)
      (reindex_reduces (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => ((p.1,p.2.1),p.2.2)) h.2)

/-- Currying respects the quotient by uniform realizability equivalence. -/
theorem curry_congr {Z X Y : RealizerPER.{u}}
    {H K : FunctionalRelation (product Z X) Y} (h : H.Equivalent K) :
    (curryRelation H).Equivalent (curryRelation K) := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : Z.Carrier × RawFunction X Y → Set ℕ := fun p => (curryRelation H).val p.1 p.2
  have hz : Reduces Γ (fun p => Z.extent p.1) := reduces_and_left _ _
  have he : Reduces Γ (fun p => (functionSpace X Y).rel (functionSlice H p.1) (functionSlice K p.1)) :=
    reduces_trans hz (reindex_reduces Prod.fst (functionSlice_congr h))
  exact reduces_and_intro hz ((functionSpace X Y).trans_of ((functionSpace X Y).symm_of he)
    (reduces_and_right _ _))

/-- The direct application relation is evaluation after the product of the arrow with the identity. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    To compare with evaluation, the same $a,b$ and strictness outputs give a realizer of
    $F\times\mathrm{id}_X$ at $((z,x),(R,x))$ and a realizer of evaluation at $((R,x),y)$.
    Pairing them proves one uniform inclusion into the composite. Both relations are functional, so
    §{sec:effective-topos-subobjects-truth-values} gives their uniform equivalence.
    Finally, a fixed conversion $F(z,R)\to G(z,R)$ acts on the first entry of $\NatPair{a}{b}$ and leaves the
    second entry unchanged. This proves preservation of uniform equivalence.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability application relation}{Application relation}]
-/
theorem uncurry_evaluation {Z X Y : RealizerPER.{u}}
    (F : FunctionalRelation Z (functionSpace X Y)) :
    (uncurryRelation F).Equivalent
      ((FunctionalRelation.pairing ((fstRelation Z X).comp F) (sndRelation Z X)).comp (evaluation X Y)) := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : ((Z.Carrier × X.Carrier) × Y.Carrier) × RawFunction X Y → Set ℕ :=
    realizabilityAnd (fun p => F.val p.1.1.1 p.2) (fun p => p.2 p.1.1.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hf : Reduces Γ (fun p => F.val p.1.1.1 p.2) := reduces_and_left _ _
  have hr : Reduces Γ (fun p => p.2 p.1.1.2 p.1.2) := reduces_and_right _ _
  have he := F.strict_right_of hf
  have hs := data_strict_of (extent_data_of he) hr
  have hz := F.strict_left_of hf
  have hx := reduces_trans hs (reduces_and_left _ _)
  have hE : Reduces Γ (fun p => (product Z X).extent p.1.1) := reduces_and_intro hz hx
  have hp : Reduces Γ (fun p => (fstRelation Z X).val p.1.1 p.1.1.1) := reduces_and_intro hE hz
  have hcomp : Reduces Γ (fun p => ((fstRelation Z X).comp F).val p.1.1 p.2) :=
    relationComp_intro hp hf
  have hq : Reduces Γ (fun p => (sndRelation Z X).val p.1.1 p.1.1.2) := reduces_and_intro hE hx
  have hpair : Reduces Γ (fun p =>
      (FunctionalRelation.pairing ((fstRelation Z X).comp F) (sndRelation Z X)).val p.1.1 (p.2,p.1.1.2)) :=
    reduces_and_intro hcomp hq
  have hev : Reduces Γ (fun p => (evaluation X Y).val (p.2,p.1.1.2) p.1.2) := reduces_and_intro he hr
  exact relationComp_intro hpair hev

open CategoryTheory

/-- Currying on equivalence classes of functional relations. -/
def curryHom {Z X Y : RealizerPER.{u}} : (product Z X ⟶ Y) → (Z ⟶ functionSpace X Y) :=
  Quotient.map curryRelation (fun _ _ h => curry_congr h)

/-- Application on equivalence classes of functional relations. -/
def uncurryHom {Z X Y : RealizerPER.{u}} : (Z ⟶ functionSpace X Y) → (product Z X ⟶ Y) :=
  Quotient.map uncurryRelation (fun _ _ h => ⟨uncurry_mono h.1,uncurry_mono h.2⟩)

/-- The hom-set bijection is witnessed by the explicit numerical constructions. -/
def realizabilityCurryEquiv (Z X Y : RealizerPER.{u}) :
    (product Z X ⟶ Y) ≃ (Z ⟶ functionSpace X Y) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv h := Quotient.inductionOn h fun H => Quotient.sound (uncurry_curry H)
  right_inv f := Quotient.inductionOn f fun F => Quotient.sound (curry_uncurry F).symm

/-- The inverse of the bijection is precisely composition with evaluation. -/
theorem uncurryHom_eq {Z X Y : RealizerPER.{u}} (f : Z ⟶ functionSpace X Y) :
    uncurryHom f = pairHom ((fstRelation Z X).toHom ≫ f) (sndRelation Z X).toHom ≫ (evaluation X Y).toHom :=
  Quotient.inductionOn f fun F => Quotient.sound (uncurry_evaluation F)

/-- Existence and uniqueness of the arrow mediating through evaluation. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{realizability exponential universal property}{Exponential universal property}]
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*} $\EffCat$ is an elementary topos.
-/
theorem realizability_exponential_unique {Z X Y : RealizerPER.{u}} (h : product Z X ⟶ Y) :
    ∃! f : Z ⟶ functionSpace X Y,
      pairHom ((fstRelation Z X).toHom ≫ f) (sndRelation Z X).toHom ≫ (evaluation X Y).toHom = h := by
  refine ⟨curryHom h, ?_, ?_⟩
  · exact (uncurryHom_eq (curryHom h)).symm.trans ((realizabilityCurryEquiv Z X Y).left_inv h)
  · intro f hf
    apply (realizabilityCurryEquiv Z X Y).symm.injective
    change uncurryHom f = uncurryHom (curryHom h)
    exact ((uncurryHom_eq f).trans hf).trans ((realizabilityCurryEquiv Z X Y).left_inv h).symm

end PolishSpaceBook.LambdaIndexPCA
