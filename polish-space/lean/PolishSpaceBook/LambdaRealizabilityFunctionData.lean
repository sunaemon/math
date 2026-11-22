module

public import PolishSpaceBook.LambdaRealizabilityClassifier

@[expose] public section

/-! # Numerical witnesses for functional relations

The four tracking indices are retained as realizers, rather than being hidden
in propositions attached to a relation. Semantic representatives are never
arguments to the lambda programs implementing abstraction and evaluation.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER
universe u

/-- A single index works at every semantic parameter. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    For families $\varphi,\psi:J\to\PowerSet{\NN}$, write
    $$\UniformTrackers{\varphi}{\psi}:=
    \{e\in\NN:\forall j\in J\ \forall a\in\varphi(j),\ e\cdot a\downarrow\in\psi(j)\}.$$
    The index must work uniformly in the semantic parameter $j$; that parameter is not an input to the program.
    For relations $R,S:|X|\times|Y|\to\PowerSet{\NN}$, use $J=|X|\times|Y|$ in $\UniformTrackers{R}{S}$.
-/
def uniformImp {J : Type*} (φ ψ : J → Set ℕ) : Set ℕ :=
  {e | ∀ j a, a ∈ φ j → ∃ b, App e a b ∧ b ∈ ψ j}

/-- Abstract a numerical input while retaining uniformity in an unencoded parameter. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the code factory from §{sec:effective-topos-construction}. On input $a$, it returns the code $c(e,a)$ of the
    program that sends $b$ to $e\cdot\NatPair{a}{b}$, without running that program.
    For every $j$, the hypothesis proves that this same code sends $\varphi(i,j)$ into $\psi(i,j)$.
    Neither the code nor its construction depends on $j$. Application uses the universal evaluator.
    For composition, abstract the numerical input after applying the first code and then the second; this again uses
    one code for all semantic parameters. Identity programs supply the reflexive case.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform tracker abstraction}{Abstraction of uniform trackers}]
-/
theorem uniformImp_intro {I J : Type*} {Γ : I → Set ℕ} {φ ψ : I → J → Set ℕ}
    (h : Reduces (realizabilityAnd (fun p : I × J => Γ p.1) (fun p => φ p.1 p.2))
      (fun p => ψ p.1 p.2)) :
    Reduces Γ (fun i => uniformImp (φ i) (ψ i)) := by
  obtain ⟨e, he⟩ := (reduces_iff _ _).mp h
  obtain ⟨outer, body, _, _, hout, hbody⟩ := exists_computable_curry_indices
  apply (reduces_iff _ _).mpr
  refine ⟨outer e, fun i a ha => ⟨body e a, hout e a, ?_⟩⟩
  intro j b hb
  obtain ⟨c, hc, hcψ⟩ := he (i,j) (Nat.pair a b) (by simpa [realizabilityAnd] using And.intro ha hb)
  exact ⟨c, (hbody e a b c).mpr hc, hcψ⟩

/-- Instantiate the semantic parameter, then run the uniform implication program. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform tracker abstraction}{Abstraction of uniform trackers}]
-/
theorem uniformImp_apply {I J : Type*} {Γ : I → Set ℕ} {φ ψ : I → J → Set ℕ}
    (hf : Reduces Γ (fun i => uniformImp (φ i) (ψ i))) (j : I → J)
    (ha : Reduces Γ (fun i => φ i (j i))) : Reduces Γ (fun i => ψ i (j i)) := by
  apply imp_apply_of (reduces_trans hf (reduces_of_subset (fun i e he => he (j i)))) ha

theorem uniformImp_identity {I J : Type*} (Γ : I → Set ℕ) (φ : I → J → Set ℕ) :
    Reduces Γ (fun i => uniformImp (φ i) (φ i)) :=
  uniformImp_intro (reduces_and_right _ _)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the code factory from §{sec:effective-topos-construction}. On input $a$, it returns the code $c(e,a)$ of the
    program that sends $b$ to $e\cdot\NatPair{a}{b}$, without running that program.
    For every $j$, the hypothesis proves that this same code sends $\varphi(i,j)$ into $\psi(i,j)$.
    Neither the code nor its construction depends on $j$. Application uses the universal evaluator.
    For composition, abstract the numerical input after applying the first code and then the second; this again uses
    one code for all semantic parameters. Identity programs supply the reflexive case.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform tracker abstraction}{Abstraction of uniform trackers}]
-/
theorem uniformImp_comp {I J : Type*} {Γ : I → Set ℕ} {φ ψ θ : I → J → Set ℕ}
    (hf : Reduces Γ (fun i => uniformImp (φ i) (ψ i)))
    (hg : Reduces Γ (fun i => uniformImp (ψ i) (θ i))) :
    Reduces Γ (fun i => uniformImp (φ i) (θ i)) := by
  apply uniformImp_intro
  have hf' := reduces_trans (reduces_and_left (fun p : I × J => Γ p.1) (fun p => φ p.1 p.2))
    (reindex_reduces Prod.fst hf)
  have hg' := reduces_trans (reduces_and_left (fun p : I × J => Γ p.1) (fun p => φ p.1 p.2))
    (reindex_reduces Prod.fst hg)
  exact uniformImp_apply hg' Prod.snd (uniformImp_apply hf' Prod.snd (reduces_and_right _ _))

abbrev RawFunction (X Y : RealizerPER.{u}) := RealizerRelation X.Carrier Y.Carrier

def strictData {X Y : RealizerPER.{u}} (R : RawFunction X Y) : Set ℕ :=
  uniformImp (fun p : X.Carrier × Y.Carrier => R p.1 p.2)
    (realizabilityAnd (fun p => X.extent p.1) (fun p => Y.extent p.2))

def extensionalData {X Y : RealizerPER.{u}} (R : RawFunction X Y) : Set ℕ :=
  uniformImp
    (realizabilityAnd
      (realizabilityAnd (fun p : X.Carrier × X.Carrier × Y.Carrier × Y.Carrier => X.rel p.1 p.2.1)
        (fun p => R p.1 p.2.2.1)) (fun p => Y.rel p.2.2.1 p.2.2.2))
    (fun p => R p.2.1 p.2.2.2)

def singleData {X Y : RealizerPER.{u}} (R : RawFunction X Y) : Set ℕ :=
  uniformImp (realizabilityAnd (fun p : X.Carrier × Y.Carrier × Y.Carrier => R p.1 p.2.1)
    (fun p => R p.1 p.2.2)) (fun p => Y.rel p.2.1 p.2.2)

def totalData {X Y : RealizerPER.{u}} (R : RawFunction X Y) : Set ℕ :=
  uniformImp X.extent (fun x => {a | ∃ y, a ∈ R x y})

/-- Nested numerical pairs of the strictness, extensionality, uniqueness, and totality indices. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    For an arbitrary relation $R:|X|\times|Y|\to\PowerSet{\NN}$, let $\FunctionalRealizers{R}$ be the set of numbers
    $$\NatPair{s}{\NatPair{e}{\NatPair{v}{t}}}$$
    whose four entries track strictness, extensionality, single-valuedness, and totality, respectively. Explicitly, they
    must satisfy all of the following conditions, uniformly in the displayed representatives:
    \begin{enumerate}
    \item If $a\in R(x,y)$, then $s\cdot a\downarrow\in E_X(x)\land E_Y(y)$.
    \item If $r\in(x\sim_X x')$, $a\in R(x,y)$, and $b\in(y\sim_Y y')$, then
    $$e\cdot\NatPair{\NatPair{r}{a}}{b}\downarrow\in R(x',y').$$
    \item If $a\in R(x,y)$ and $b\in R(x,y')$, then
    $$v\cdot\NatPair{a}{b}\downarrow\in(y\sim_Y y').$$
    \item If $r\in E_X(x)$, then
    $$t\cdot r\downarrow\in\bigcup_{y\in|Y|}R(x,y).$$
    \end{enumerate}
    The last output is a realizer in the union; it need not encode a representative $y$.
-/
def functionData {X Y : RealizerPER.{u}} (R : RawFunction X Y) : Set ℕ :=
  {a | a.unpair.1 ∈ strictData R ∧ a.unpair.2.unpair.1 ∈ extensionalData R ∧
    a.unpair.2.unpair.2.unpair.1 ∈ singleData R ∧ a.unpair.2.unpair.2.unpair.2 ∈ totalData R}

theorem functionData_inhabited_iff {X Y : RealizerPER.{u}} (R : RawFunction X Y) :
    (functionData R).Nonempty ↔ ∃ F : FunctionalRelation X Y, F.val = R := by
  constructor
  · rintro ⟨a, hs, he, hv, ht⟩
    exact ⟨⟨R, (reduces_iff _ _).mpr ⟨a.unpair.1, hs⟩,
      (reduces_iff _ _).mpr ⟨a.unpair.2.unpair.1, he⟩,
      (reduces_iff _ _).mpr ⟨a.unpair.2.unpair.2.unpair.1, hv⟩,
      (reduces_iff _ _).mpr ⟨a.unpair.2.unpair.2.unpair.2, ht⟩⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    obtain ⟨s, hs⟩ := (reduces_iff _ _).mp F.strict
    obtain ⟨e, he⟩ := (reduces_iff _ _).mp F.extensional
    obtain ⟨v, hv⟩ := (reduces_iff _ _).mp F.single
    obtain ⟨t, ht⟩ := (reduces_iff _ _).mp F.total
    refine ⟨Nat.pair s (Nat.pair e (Nat.pair v t)), ?_⟩
    simpa only [functionData, strictData, extensionalData, singleData, totalData, uniformImp, Set.mem_ofPred_eq, Nat.unpair_pair] using
      And.intro hs (And.intro he (And.intro hv ht))

/-- One numerical transformer converts every value of one relation to the other. -/
def relationEntailment {X Y : RealizerPER.{u}} (R S : RawFunction X Y) : Set ℕ :=
  uniformImp (fun p : X.Carrier × Y.Carrier => R p.1 p.2) (fun p => S p.1 p.2)

/-- The candidate exponential retains the tracking data at both endpoints of equality. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability function object}{Function object and evaluation}]
-/
def functionSpace (X Y : RealizerPER.{u}) : RealizerPER.{u} where
  Carrier := RawFunction X Y
  rel R S := {a | (a.unpair.1.unpair.1 ∈ functionData R ∧ a.unpair.1.unpair.2 ∈ functionData S) ∧
    a.unpair.2.unpair.1 ∈ relationEntailment R S ∧ a.unpair.2.unpair.2 ∈ relationEntailment S R}
  symmetry := reduces_and_intro
    (reduces_and_intro (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)))
    (reduces_and_intro (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
  transitivity := reduces_and_intro
    (reduces_and_intro
      (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_left _ _))
      (reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)) (reduces_and_right _ _)))
    (reduces_and_intro
      (uniformImp_comp
        (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_left _ _))
        (reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)) (reduces_and_left _ _)))
      (uniformImp_comp
        (reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)) (reduces_and_right _ _))
        (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) (reduces_and_right _ _))))

/-- A tuple of the four indices supplies the extent by adjoining identity conversions. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Symmetry exchanges the two data tuples and the two conversion indices. Transitivity retains the data at the first
    and last endpoints and composes the conversion indices in the appropriate directions by the preceding lemma.
    This proves the PER laws uniformly. Its extent projects to $\FunctionalRealizers{R}$. Conversely, a number in
    $\FunctionalRealizers{R}$ can be duplicated and paired with two identity-conversion indices to realize the extent.
    Thus the extent and $\FunctionalRealizers{R}$ are uniformly equivalent.
    By the definition of that set, an element supplies the four tracking indices of a functional relation, and any
    functional relation supplies such a tuple. This proves the assertion about inhabited extent.
-/
theorem functionData_extent {X Y : RealizerPER.{u}} :
    Reduces (functionData (X := X) (Y := Y)) (functionSpace X Y).extent :=
  reduces_and_intro (reduces_and_intro (reduces_refl _) (reduces_refl _))
    (reduces_and_intro (uniformImp_identity _ (fun (R : RawFunction X Y) (p : X.Carrier × Y.Carrier) => R p.1 p.2))
      (uniformImp_identity _ (fun (R : RawFunction X Y) (p : X.Carrier × Y.Carrier) => R p.1 p.2)))

theorem extent_functionData {X Y : RealizerPER.{u}} :
    Reduces (functionSpace X Y).extent (functionData (X := X) (Y := Y)) := by
  change Reduces (realizabilityAnd (realizabilityAnd (functionData (X := X) (Y := Y)) functionData)
    (realizabilityAnd (fun R => relationEntailment R R) (fun R => relationEntailment R R))) functionData
  exact reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)

/-- Precisely the functional relations have inhabited extent in the function object. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Symmetry exchanges the two data tuples and the two conversion indices. Transitivity retains the data at the first
    and last endpoints and composes the conversion indices in the appropriate directions by the preceding lemma.
    This proves the PER laws uniformly. Its extent projects to $\FunctionalRealizers{R}$. Conversely, a number in
    $\FunctionalRealizers{R}$ can be duplicated and paired with two identity-conversion indices to realize the extent.
    Thus the extent and $\FunctionalRealizers{R}$ are uniformly equivalent.
    By the definition of that set, an element supplies the four tracking indices of a functional relation, and any
    functional relation supplies such a tuple. This proves the assertion about inhabited extent.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability function object}{Function object and evaluation}]
-/
theorem functionSpace_extent_inhabited_iff {X Y : RealizerPER.{u}} (R : RawFunction X Y) :
    ((functionSpace X Y).extent R).Nonempty ↔ ∃ F : FunctionalRelation X Y, F.val = R := by
  rw [← functionData_inhabited_iff]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨e, he⟩ := (reduces_iff _ _).mp (extent_functionData (X := X) (Y := Y))
    obtain ⟨b, _, hb⟩ := he R a ha
    exact ⟨b, hb⟩
  · rintro ⟨a, ha⟩
    obtain ⟨e, he⟩ := (reduces_iff _ _).mp (functionData_extent (X := X) (Y := Y))
    obtain ⟨b, _, hb⟩ := he R a ha
    exact ⟨b, hb⟩

section DataProjections
variable {X Y : RealizerPER.{u}}

theorem data_strict : Reduces (functionData (X := X) (Y := Y)) strictData := by
  change Reduces (realizabilityAnd strictData (realizabilityAnd extensionalData
    (realizabilityAnd singleData totalData))) strictData
  exact reduces_and_left _ _

theorem data_extensional : Reduces (functionData (X := X) (Y := Y)) extensionalData := by
  change Reduces (realizabilityAnd strictData (realizabilityAnd extensionalData
    (realizabilityAnd singleData totalData))) extensionalData
  exact reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)

theorem data_single : Reduces (functionData (X := X) (Y := Y)) singleData := by
  change Reduces (realizabilityAnd strictData (realizabilityAnd extensionalData
    (realizabilityAnd singleData totalData))) singleData
  exact reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)) (reduces_and_left _ _)

theorem data_total : Reduces (functionData (X := X) (Y := Y)) totalData := by
  change Reduces (realizabilityAnd strictData (realizabilityAnd extensionalData
    (realizabilityAnd singleData totalData))) totalData
  exact reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)) (reduces_and_right _ _)

theorem extent_data_of {I : Type*} {Γ : I → Set ℕ} {R : I → RawFunction X Y}
    (h : Reduces Γ (fun i => (functionSpace X Y).extent (R i))) :
    Reduces Γ (fun i => functionData (R i)) :=
  reduces_trans h (reindex_reduces R extent_functionData)

end DataProjections

end PolishSpaceBook.LambdaIndexPCA
