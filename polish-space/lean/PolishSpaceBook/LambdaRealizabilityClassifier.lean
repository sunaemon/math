module

public import PolishSpaceBook.LambdaRealizabilityTruthValues
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs

@[expose] public section

/-! # The subobject classifier of the lambda-realizability PER category

The truth relation has value `S` at a truth-value representative `S`. The
pullback factorization transforms numerical realizers without selecting a
representative from an existential union.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory Limits RealizerPER
universe u

/-- The functional relation representing truth at the terminal object. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First verify the four conditions for the truth relation. Strictness supplies an arbitrary natural number as the
    terminal extent and uses the two identity implications for the extent of $S$.
    Extensionality applies the forward implication in $S\sim_\Omega T$ to the input in $S$.
    For single-valuedness, realizers $s\in S$ and $t\in T$ give constant programs with values $t$ and $s$, respectively;
    parameter abstraction supplies codes realizing both implications. Totality uses $S=\NN$ and retains the input.
    This proves that the relation is functional. It is monic because its domain is terminal.
-/
def truthRelation : FunctionalRelation RealizerPER.terminal.{u} truthValues.{u} where
  val _ S := S.down
  strict := reduces_and_intro (reduces_top _) (truth_extent _ Prod.snd)
  extensional := imp_apply_of (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _))
    (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
  single := reduces_and_intro
    ((reduces_imp_iff _ _ _).mp (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)))
    ((reduces_imp_iff _ _ _).mp (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)))
  total := reduces_of_subset fun _ a _ => ⟨⟨Set.univ⟩, Set.mem_univ a⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{realizability subobject classifier}{Subobject classifier in realizability}]
-/
instance truthRelation_mono : Mono (C := RealizerPER.{u}) truthRelation.toHom :=
  terminalIsTerminal.mono_from _

/-- The representative map selecting the full truth value. -/
def topTruthMap : Map RealizerPER.terminal.{u} truthValues.{u} where
  toFun _ := ⟨Set.univ⟩
  preserves := truth_extent.{u} _ (fun _ => ⟨Set.univ⟩)

/-- Truth is the graph of the full truth value, up to uniform equivalence. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    This relation also agrees with the graph of the representative map $\ast\mapsto\NN$.
    Indeed, from an input in $S$ one obtains an implication $\NN\to S$ by a constant program, while the reverse
    implication has unrestricted output. These codes and the terminal extent give the graph realizer.
    The uniform inclusion between the two functional relations is an equivalence by the preceding proof.
-/
theorem truthRelation_top_graph :
    FunctionalRelation.Equivalent truthRelation.{u} topTruthMap.graph := by
  apply FunctionalRelation.equivalent_of_le
  apply reduces_and_intro (reduces_top _)
  apply reduces_and_intro
  · exact (reduces_imp_iff _ _ _).mp (reduces_and_left _ _)
  · exact imp_of_reduces _ (reduces_top _)

/-- Commutativity of the predicate-classification square. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    To check commutativity, take realizers of $J_\varphi(x,x')$ and $\chi_\varphi(x',S)$.
    The first supplies $x\sim_X x'$ and $\varphi(x)$. Extensionality of the predicate gives $\varphi(x')$, and the
    forward implication from the second realizer gives an element of $S$.
    The first realizer also supplies $E_{\PERRestriction{X}{\varphi}}(x)$.
    Pairing these outputs realizes $(\RealizabilityTruthArrow\circ T_{\PERRestriction{X}{\varphi}})(x,S)$, using the
    intermediate point $\ast$. This is a uniform reduction from $\chi_\varphi\circ J_\varphi$ to
    $\RealizabilityTruthArrow\circ T_{\PERRestriction{X}{\varphi}}$. Again, an inclusion between functional relations
    is an equivalence, so the square commutes.
-/
theorem characteristic_inclusion_condition {X : RealizerPER.{u}} (P : StrictPredicate X) :
    FunctionalRelation.Equivalent
      (FunctionalRelation.comp P.inclusion (characteristic P))
      (FunctionalRelation.comp (toTerminal P.restriction) truthRelation) := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : (X.Carrier × truthValues.{u}.Carrier) × X.Carrier → Set ℕ :=
    realizabilityAnd (fun p => P.inclusion.val p.1.1 p.2)
      (fun p => (characteristic P).val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hE : Reduces Γ (fun p => P.restriction.extent p.1.1) :=
    P.inclusion.strict_left_of (reduces_and_left _ _)
  have hP : Reduces Γ (fun p => P.val p.2) :=
    reduces_trans (reduces_and_left _ _)
      (reindex_reduces (fun p : (X.Carrier × truthValues.{u}.Carrier) × X.Carrier => (p.1.1, p.2)) P.extensional)
  have hS : Reduces Γ (fun p => p.1.2.down) :=
    imp_apply_of (reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
      (reduces_and_left _ _)) hP
  exact relationComp_intro (I := (X.Carrier × truthValues.{u}.Carrier) × X.Carrier)
    (F := (toTerminal P.restriction).val) (G := truthRelation.val)
    (x := fun p => p.1.1) (y := fun _ => PUnit.unit) (z := fun p => p.1.2) hE hS

/-- A composite through truth contains a realizer of its target truth value. -/
theorem truth_of_composite {Z : RealizerPER.{u}} (K : FunctionalRelation Z RealizerPER.terminal.{u}) :
    Reduces (fun p : Z.Carrier × truthValues.{u}.Carrier =>
      (FunctionalRelation.comp K truthRelation).val p.1 p.2) (fun p => p.2.down) := by
  apply reduces_cover (θ := realizabilityAnd
    (fun p : (Z.Carrier × truthValues.{u}.Carrier) × RealizerPER.terminal.{u}.Carrier => K.val p.1.1 p.2)
    (fun p => p.1.2.down)) (fun _ _ h => h)
  exact reduces_and_right _ _

/-- The commuting-square equation yields a uniform predicate realizer at every output of H. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the universal property, suppose functional relations $H:Z\to X$ and $K:Z\to1$ satisfy
    $$\chi_\varphi\circ H\equiv\RealizabilityTruthArrow\circ K$$
    and fix a tracker $c$ for the forward reduction. Given $a\in H(z,x)$, strictness gives $E_X(x)$, and the two
    identity implications give $\varphi(x)\sim_\Omega\varphi(x)$.
    Together they form, uniformly in $a$, a realizer
    $$g(a)\in\chi_\varphi(x,\varphi(x)).$$
    Thus $\NatPair{a}{g(a)}$ realizes the left composite at $\varphi(x)$. Compute
    $$\NatPair{b_0}{b_1}=c\cdot\NatPair{a}{g(a)}.$$
    By the defining value of the truth relation, $b_1\in\varphi(x)$. Projecting this numerical pair proves
    $H(z,x)\le\varphi(x)$ uniformly. The restriction lemma now gives a factorization $L:Z\to\PERRestriction{X}{\varphi}$
    with $J_\varphi\circ L=H$. Its composite with the arrow to $1$ is $K$, by uniqueness of arrows to a terminal object.
    The factorization is unique because $J_\varphi$ is monic. This proves the pullback property.
-/
theorem predicate_of_commuting_square {X Z : RealizerPER.{u}} (P : StrictPredicate X)
    (H : FunctionalRelation Z X) (K : FunctionalRelation Z RealizerPER.terminal.{u})
    (h : FunctionalRelation.Equivalent (FunctionalRelation.comp H (characteristic P))
      (FunctionalRelation.comp K truthRelation)) :
    Reduces (fun p : Z.Carrier × X.Carrier => H.val p.1 p.2) (fun p => P.val p.2) := by
  let Γ : Z.Carrier × X.Carrier → Set ℕ := fun p => H.val p.1 p.2
  have hc : Reduces Γ (fun p => (characteristic P).val p.2 ⟨P.val p.2⟩) :=
    reduces_and_intro (H.strict_right_of (reduces_refl _))
      (truth_extent.{u} Γ (fun p => ⟨P.val p.2⟩))
  have hh : Reduces Γ (fun p => (FunctionalRelation.comp H (characteristic P)).val p.1 ⟨P.val p.2⟩) :=
    relationComp_intro (F := H.val) (G := (characteristic P).val)
      (x := Prod.fst) (y := Prod.snd) (z := fun p => ⟨P.val p.2⟩) (reduces_refl _) hc
  exact reduces_trans hh (reindex_reduces (fun p : Z.Carrier × X.Carrier => (p.1, (⟨P.val p.2⟩ : truthValues.{u}.Carrier)))
    (reduces_trans h.1 (truth_of_composite K)))

theorem classifier_exists_lift {X Z : RealizerPER.{u}} (P : StrictPredicate X)
    (h : Z ⟶ X) (k : Z ⟶ RealizerPER.terminal.{u})
    (w : h ≫ (characteristic P).toHom = k ≫ truthRelation.toHom) :
    ∃ l : Z ⟶ P.restriction, l ≫ P.inclusion.toHom = h := by
  revert w
  refine Quotient.inductionOn₂ h k fun H K w => ?_
  have he := (FunctionalRelation.toHom_eq_iff _ _).mp w
  let hp := predicate_of_commuting_square P H K he
  exact ⟨(P.lift H hp).toHom, Quotient.sound (P.lift_inclusion H hp)⟩

/-- The square for a predicate inclusion is a categorical pullback. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the universal property, suppose functional relations $H:Z\to X$ and $K:Z\to1$ satisfy
    $$\chi_\varphi\circ H\equiv\RealizabilityTruthArrow\circ K$$
    and fix a tracker $c$ for the forward reduction. Given $a\in H(z,x)$, strictness gives $E_X(x)$, and the two
    identity implications give $\varphi(x)\sim_\Omega\varphi(x)$.
    Together they form, uniformly in $a$, a realizer
    $$g(a)\in\chi_\varphi(x,\varphi(x)).$$
    Thus $\NatPair{a}{g(a)}$ realizes the left composite at $\varphi(x)$. Compute
    $$\NatPair{b_0}{b_1}=c\cdot\NatPair{a}{g(a)}.$$
    By the defining value of the truth relation, $b_1\in\varphi(x)$. Projecting this numerical pair proves
    $H(z,x)\le\varphi(x)$ uniformly. The restriction lemma now gives a factorization $L:Z\to\PERRestriction{X}{\varphi}$
    with $J_\varphi\circ L=H$. Its composite with the arrow to $1$ is $K$, by uniqueness of arrows to a terminal object.
    The factorization is unique because $J_\varphi$ is monic. This proves the pullback property.
-/
theorem characteristic_isPullback {X : RealizerPER.{u}} (P : StrictPredicate X) :
    IsPullback (C := RealizerPER.{u}) P.inclusion.toHom (toTerminal P.restriction).toHom
      (characteristic P).toHom truthRelation.toHom := by
  classical
  have w := (FunctionalRelation.toHom_eq_iff _ _).mpr (characteristic_inclusion_condition P)
  apply IsPullback.of_isLimit (c := PullbackCone.mk (C := RealizerPER.{u}) _ _ w)
  refine PullbackCone.IsLimit.mk w
    (fun s => (classifier_exists_lift P s.fst s.snd s.condition).choose) ?_ ?_ ?_
  · intro s
    exact (classifier_exists_lift P s.fst s.snd s.condition).choose_spec
  · intro s
    exact terminalIsTerminal.hom_ext _ _
  · intro s m hm _
    exact P.inclusion_cancel m _ (hm.trans
      (classifier_exists_lift P s.fst s.snd s.condition).choose_spec.symm)

/-- Existence and uniqueness of a characteristic arrow for every monomorphism. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For a general monomorphism $m:U\to X$ represented by $M$, the predicate presentation already proved gives
    an isomorphism $e:U\cong\PERRestriction{X}{\varphi_M}$ over $X$.
    Transporting the preceding pullback along this isomorphism gives the classifying square for
    $\chi_{\varphi_M}$. Suppose another arrow $f:X\to\RealizabilityTruthValues$ gives a pullback with the same $m$.
    Write $f=\chi_\psi$ using the truth-value normal form. Its canonical pullback is $J_\psi$.
    Uniqueness of pullbacks gives an isomorphism over $X$ between the two predicate restrictions.
    The predicate-presentation result therefore gives $\varphi_M\equiv\psi$ uniformly.
    By the uniqueness result for characteristic relations, $f=\chi_{\varphi_M}$.
    This proves the universal property for every monomorphism, including uniqueness of its characteristic arrow.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{realizability subobject classifier}{Subobject classifier in realizability}]
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*} $\EffCat$ is an elementary topos.
-/
theorem existsUnique_classifier {U X : RealizerPER.{u}} (m : U ⟶ X) [Mono m] :
    ∃! f : X ⟶ truthValues.{u},
      IsPullback (C := RealizerPER.{u}) m (toTerminal U).toHom f truthRelation.toHom := by
  obtain ⟨P, e, he⟩ := mono_is_predicate_restriction m inferInstance
  have hp : IsPullback (C := RealizerPER.{u}) m (toTerminal U).toHom
      (characteristic P).toHom truthRelation.toHom := by
    apply (characteristic_isPullback P).of_iso' e (Iso.refl X)
      (Iso.refl RealizerPER.terminal.{u}) (Iso.refl truthValues.{u})
    · simpa using he
    · exact terminalIsTerminal.hom_ext _ _
    · simp
    · simp
  refine ⟨(characteristic P).toHom, hp, ?_⟩
  intro f hf
  obtain ⟨Q, rfl⟩ := exists_characteristic f
  let eQ : U ≅ Q.restriction := hf.isoIsPullback X RealizerPER.terminal.{u} (characteristic_isPullback Q)
  have hQ : eQ.hom ≫ Q.inclusion.toHom = m :=
    hf.isoIsPullback_hom_fst X RealizerPER.terminal.{u} (characteristic_isPullback Q)
  have hePQ : (e.symm ≪≫ eQ).hom ≫ Q.inclusion.toHom = P.inclusion.toHom := by
    change (e.inv ≫ eQ.hom) ≫ Q.inclusion.toHom = P.inclusion.toHom
    rw [Category.assoc, hQ, ← he, e.inv_hom_id_assoc]
  have hPQ := P.equivalent_of_iso Q (e.symm ≪≫ eQ) hePQ
  exact ((characteristic_eq_iff P Q).mpr hPQ).symm

/-- The classifier uses mathlib's canonical structure and categorical universal property. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{realizability subobject classifier}{Subobject classifier in realizability}]
-/
noncomputable def realizabilityClassifier : CategoryTheory.Subobject.Classifier RealizerPER.{u} where
  Ω₀ := RealizerPER.terminal
  Ω := truthValues
  truth := truthRelation.toHom
  χ₀ U := (toTerminal U).toHom
  χ m _ := (existsUnique_classifier m).choose
  isPullback m _ := (existsUnique_classifier m).choose_spec.1
  uniq {U X} m _ {χ₀'} {χ'} h := by
    have ht : χ₀' = (toTerminal U).toHom := terminalIsTerminal.hom_ext _ _
    subst χ₀'
    exact (existsUnique_classifier m).choose_spec.2 χ' h

instance realizabilityHasSubobjectClassifier : HasSubobjectClassifier RealizerPER.{u} :=
  ⟨⟨realizabilityClassifier⟩⟩

end PolishSpaceBook.LambdaIndexPCA
