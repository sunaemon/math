module

public import PolishSpaceBook.LambdaRealizabilitySubobjects

@[expose] public section

/-! # Truth values and normal forms of arrows into the truth-value PER -/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory RealizerPER
universe u

theorem imp_apply_of {I : Type*} {Γ φ ψ : I → Set ℕ}
    (hf : Reduces Γ (realizabilityImp φ ψ)) (ha : Reduces Γ φ) : Reduces Γ ψ :=
  reduces_trans (reduces_and_intro hf ha)
    ((reduces_imp_iff _ φ ψ).mpr (reduces_refl _))

theorem imp_comp_of {I : Type*} {Γ φ ψ θ : I → Set ℕ}
    (h₁ : Reduces Γ (realizabilityImp φ ψ)) (h₂ : Reduces Γ (realizabilityImp ψ θ)) :
    Reduces Γ (realizabilityImp φ θ) := by
  apply (reduces_imp_iff _ _ _).mp
  exact imp_apply_of (reduces_trans (reduces_and_left _ _) h₂)
    (imp_apply_of (reduces_trans (reduces_and_left _ _) h₁) (reduces_and_right _ _))

theorem imp_identity {I : Type*} (Γ φ : I → Set ℕ) : Reduces Γ (realizabilityImp φ φ) :=
  (reduces_imp_iff _ _ _).mp (reduces_and_right _ _)

def truthImp (S T : Set ℕ) : Set ℕ := {e | ∀ a, a ∈ S → ∃ b, App e a b ∧ b ∈ T}

/-- Universe lifting changes only the ambient type of the representatives. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability truth-value object}{Truth values and characteristic relations}]
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In $\EffCat$, $\SubobjectClassifier$ is the PER object of
    propositions with equality witnessed by implications in both directions, as described in
    §{sec:effective-topos-construction}.
-/
def truthValues : RealizerPER.{u} where
  Carrier := ULift.{u} (Set ℕ)
  rel S T := {a | a.unpair.1 ∈ truthImp S.down T.down ∧ a.unpair.2 ∈ truthImp T.down S.down}
  symmetry := reduces_and_intro (reduces_and_right _ _) (reduces_and_left _ _)
  transitivity := reduces_and_intro
    (imp_comp_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
    (imp_comp_of (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)))

theorem truth_extent {I : Type*} (Γ : I → Set ℕ) (S : I → truthValues.{u}.Carrier) :
    Reduces Γ (fun i => truthValues.extent (S i)) :=
  reduces_and_intro (imp_identity Γ (fun i => (S i).down)) (imp_identity Γ (fun i => (S i).down))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Symmetry exchanges the two implication realizers. Transitivity composes them in the appropriate directions, using the
    implication adjunction proved in §{sec:effective-topos-construction}. Identity implications supply extent realizers
    uniformly for every $S$, so $\sigma$ is strict. From $S\sim_\Omega T$ and a realizer in $S$, applying the first
    implication realizer returns one in $T$, proving extensionality of $\sigma$.
    For $\chi_\varphi$, an $X$-equality realizer gives a transformer from $\varphi(x)$ to $\varphi(x')$ by extensionality,
    and symmetry gives the reverse transformer. Parameter abstraction turns these into the two implication codes,
    so the representative map $x\mapsto\varphi(x)$ uniformly preserves equality. Its graph relation from
    §{sec:effective-topos-finite-limits} is exactly the displayed $\chi_\varphi$.
-/
def genericTruthPredicate : StrictPredicate truthValues.{u} where
  val S := S.down
  strict := truth_extent _ id
  extensional := imp_apply_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
    (reduces_and_right _ _)

/-- Extensionality supplies both implications by parameter abstraction. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Symmetry exchanges the two implication realizers. Transitivity composes them in the appropriate directions, using the
    implication adjunction proved in §{sec:effective-topos-construction}. Identity implications supply extent realizers
    uniformly for every $S$, so $\sigma$ is strict. From $S\sim_\Omega T$ and a realizer in $S$, applying the first
    implication realizer returns one in $T$, proving extensionality of $\sigma$.
    For $\chi_\varphi$, an $X$-equality realizer gives a transformer from $\varphi(x)$ to $\varphi(x')$ by extensionality,
    and symmetry gives the reverse transformer. Parameter abstraction turns these into the two implication codes,
    so the representative map $x\mapsto\varphi(x)$ uniformly preserves equality. Its graph relation from
    §{sec:effective-topos-finite-limits} is exactly the displayed $\chi_\varphi$.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In $\EffCat$, $\SubobjectClassifier$ is the PER object of
    propositions with equality witnessed by implications in both directions, as described in
    §{sec:effective-topos-construction}.
-/
def characteristicMap {X : RealizerPER.{u}} (P : StrictPredicate X) : Map X truthValues.{u} where
  toFun x := ⟨P.val x⟩
  preserves := by
    apply reduces_and_intro
    · exact (reduces_imp_iff _ _ _).mp P.extensional
    · apply (reduces_imp_iff _ _ _).mp
      exact reduces_trans (reduces_and_intro (X.symm_of (reduces_and_left _ _)) (reduces_and_right _ _))
        (reindex_reduces (fun p : X.Carrier × X.Carrier => (p.2, p.1)) P.extensional)

abbrev characteristic {X : RealizerPER.{u}} (P : StrictPredicate X) := (characteristicMap P).graph

namespace FunctionalRelation

/-- Pull the generic truth predicate back at the level of uniform realizer predicates. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For a given $F$, strictness of $D_F$ follows by applying strictness of $F$ to the first component. For
    extensionality, transport that $F$ realizer along equality in $X$ and retain the second component in the same $S$.
    To prove $F\le\chi_{D_F}$, fix $a\in F(x,S)$. Strictness supplies $E_X(x)$. The transformation
    $$s\longmapsto\NatPair{a}{s}$$
    sends $S$ into $D_F(x)$. In the other direction, a realizer $\NatPair{b}{t}$ of $D_F(x)$ has
    $b\in F(x,T)$ and $t\in T$ for some $T$. Single-valuedness applied to $a,b$ returns a realizer of
    $S\sim_\Omega T$. Apply its second implication to $t$ to obtain an element of $S$.
    These two transformations are uniform in $a$; parameter abstraction gives the implication codes witnessing
    $D_F(x)\sim_\Omega S$. Pairing with the extent realizer proves $F\le\chi_{D_F}$, and the preceding observation
    proves equivalence.
-/
def truthPredicate {X : RealizerPER.{u}} (F : FunctionalRelation X truthValues.{u}) : StrictPredicate X where
  val x := {a | ∃ S : truthValues.{u}.Carrier, a.unpair.1 ∈ F.val x S ∧ a.unpair.2 ∈ S.down}
  strict := by
    apply reduces_cover (θ := realizabilityAnd
      (fun p : X.Carrier × truthValues.{u}.Carrier => F.val p.1 p.2) (fun p => p.2.down)) (fun _ _ h => h)
    exact F.strict_left_of (reduces_and_left _ _)
  extensional := by
    let Γ : (X.Carrier × X.Carrier) × truthValues.{u}.Carrier → Set ℕ :=
      realizabilityAnd (fun p => X.rel p.1.1 p.1.2)
        (realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => p.2.down))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨S, hS⟩⟩
      exact ⟨S, hr, hS⟩
    · have hF : Reduces Γ (fun p => F.val p.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      apply reduces_trans (reduces_and_intro
        (F.ext_of (reduces_and_left _ _) hF (F.strict_right_of hF))
        (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-- Every arrow into Ω is the characteristic relation of its truth predicate. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For a given $F$, strictness of $D_F$ follows by applying strictness of $F$ to the first component. For
    extensionality, transport that $F$ realizer along equality in $X$ and retain the second component in the same $S$.
    To prove $F\le\chi_{D_F}$, fix $a\in F(x,S)$. Strictness supplies $E_X(x)$. The transformation
    $$s\longmapsto\NatPair{a}{s}$$
    sends $S$ into $D_F(x)$. In the other direction, a realizer $\NatPair{b}{t}$ of $D_F(x)$ has
    $b\in F(x,T)$ and $t\in T$ for some $T$. Single-valuedness applied to $a,b$ returns a realizer of
    $S\sim_\Omega T$. Apply its second implication to $t$ to obtain an element of $S$.
    These two transformations are uniform in $a$; parameter abstraction gives the implication codes witnessing
    $D_F(x)\sim_\Omega S$. Pairing with the extent realizer proves $F\le\chi_{D_F}$, and the preceding observation
    proves equivalence.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability truth-value object}{Truth values and characteristic relations}]
-/
theorem truthPredicate_characteristic {X : RealizerPER.{u}} (F : FunctionalRelation X truthValues.{u}) :
    Equivalent F (characteristic F.truthPredicate) := by
  apply equivalent_of_le
  apply reduces_and_intro (F.strict_left_of (reduces_refl _))
  apply reduces_and_intro
  · apply (reduces_imp_iff _ _ _).mp
    let Γ : (X.Carrier × truthValues.{u}.Carrier) × truthValues.{u}.Carrier → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.1.2)
        (realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => p.2.down))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨ha, ⟨T, hT⟩⟩
      exact ⟨T, ha, hT⟩
    · exact imp_apply_of
        (reduces_trans
          (F.single_of (reduces_and_left _ _) (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
          (reduces_and_right _ _))
        (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  · apply (reduces_imp_iff _ _ _).mp
    exact reduces_of_subset fun p _ h => ⟨p.2, h⟩


theorem truthPredicate_mono {X : RealizerPER.{u}} {F G : FunctionalRelation X truthValues.{u}}
    (h : LE F G) : Reduces F.truthPredicate.val G.truthPredicate.val := by
  apply reduces_cover (θ := realizabilityAnd
    (fun p : X.Carrier × truthValues.{u}.Carrier => F.val p.1 p.2) (fun p => p.2.down)) (fun _ _ h => h)
  apply reduces_trans (and_reduces_mono h (reduces_refl _))
  exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For $F=\chi_\varphi$, the construction recovers $\varphi$ up to uniform equivalence. A realizer of $D_{\chi_\varphi}(x)$
    contains an $S$ realizer and an implication $S\to\varphi(x)$, which together give a $\varphi(x)$ realizer.
    Conversely, a $\varphi(x)$ realizer gives the source extent by strictness. Pair it with an extent realizer of
    $\varphi(x)$ in the truth-value PER to obtain a $\chi_\varphi(x,\varphi(x))$ realizer, and pair that output with the
    original input. This realizes $D_{\chi_\varphi}(x)$. Hence
    $$D_{\chi_\varphi}\equiv\varphi.$$
    The sets of realizer numbers need not be literally equal.
-/
theorem truthPredicate_characteristic_recover {X : RealizerPER.{u}} (P : StrictPredicate X) :
    Reduces (characteristic P).truthPredicate.val P.val ∧
      Reduces P.val (characteristic P).truthPredicate.val := by
  constructor
  · let Γ : X.Carrier × truthValues.{u}.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (characteristic P).val p.1 p.2) (fun p => p.2.down)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact imp_apply_of
      (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
        (reduces_and_right _ _)) (reduces_and_right _ _)
  · have hg : Reduces P.val (fun x => (characteristic P).val x ⟨P.val x⟩) :=
      reduces_and_intro P.strict (truth_extent.{u} _ (fun x => ⟨P.val x⟩))
    apply reduces_trans (reduces_and_intro hg (reduces_refl _))
    exact reduces_of_subset fun x _ h => ⟨⟨P.val x⟩, h⟩

end FunctionalRelation

theorem imp_of_reduces {I : Type*} (Γ : I → Set ℕ) {φ ψ : I → Set ℕ} (h : Reduces φ ψ) :
    Reduces Γ (realizabilityImp φ ψ) :=
  (reduces_imp_iff _ _ _).mp (reduces_trans (reduces_and_right _ _) h)

/-- The characteristic arrow depends exactly on the uniform-equivalence class of the predicate. -/
theorem characteristic_equivalent {X : RealizerPER.{u}} (P Q : StrictPredicate X)
    (hPQ : Reduces P.val Q.val) (hQP : Reduces Q.val P.val) :
    FunctionalRelation.Equivalent (characteristic P) (characteristic Q) := by
  apply FunctionalRelation.equivalent_of_le
  exact reduces_and_intro (reduces_and_left _ _)
    (reduces_and_intro
      (imp_comp_of (imp_of_reduces _ (reindex_reduces Prod.fst hQP))
        (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
      (imp_comp_of (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
        (imp_of_reduces _ (reindex_reduces Prod.fst hPQ))))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    If $\varphi\equiv\psi$, the two uniform reductions give implication codes between $\varphi(x)$ and $\psi(x)$.
    Composing them with a realizer of $\varphi(x)\sim_\Omega S$ gives one of $\psi(x)\sim_\Omega S$ while preserving
    the source extent. Thus $\chi_\varphi\equiv\chi_\psi$. Conversely, a uniform reduction between two functional
    relations preserves their $D$ predicates: transform the relation realizer and retain the truth-value realizer.
    Applying this to both directions of $\chi_\varphi\equiv\chi_\psi$, then using the recovery just proved, gives
    $\varphi\equiv\psi$. This proves the asserted uniqueness.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability truth-value object}{Truth values and characteristic relations}]
-/
theorem characteristic_eq_iff {X : RealizerPER.{u}} (P Q : StrictPredicate X) :
    (characteristic P).toHom = (characteristic Q).toHom ↔ Reduces P.val Q.val ∧ Reduces Q.val P.val := by
  constructor
  · intro h
    have he := (FunctionalRelation.toHom_eq_iff _ _).mp h
    have hP := FunctionalRelation.truthPredicate_characteristic_recover P
    have hQ := FunctionalRelation.truthPredicate_characteristic_recover Q
    exact ⟨reduces_trans hP.2 (reduces_trans (FunctionalRelation.truthPredicate_mono he.1) hQ.1),
      reduces_trans hQ.2 (reduces_trans (FunctionalRelation.truthPredicate_mono he.2) hP.1)⟩
  · rintro ⟨hPQ, hQP⟩
    exact Quotient.sound (characteristic_equivalent P Q hPQ hQP)

/-- Every categorical arrow has a predicate presentation; uniqueness is the preceding equivalence. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability truth-value object}{Truth values and characteristic relations}]
-/
theorem exists_characteristic {X : RealizerPER.{u}} (f : X ⟶ truthValues.{u}) :
    ∃ P : StrictPredicate X, f = (characteristic P).toHom :=
  Quotient.inductionOn f fun F => ⟨F.truthPredicate, Quotient.sound F.truthPredicate_characteristic⟩

end PolishSpaceBook.LambdaIndexPCA
