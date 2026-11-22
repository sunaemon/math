module

public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

/-!
# Computable Polish spaces and type-two effectivity

Formalization targets for
`polish-space/src/polish-space-book/computable-polish-spaces-tte.md`.

This file formalizes a bounded structural core: extensional realizers between
represented spaces, their identity and composition laws, the realizer part of
the product criterion, the two metric margin estimates used for basic balls
and output Cauchy names, abstract Martin-Löf and weak-2 test predicates, and a
typed name-level formulation of ordinary and strong Weihrauch reduction.

`LambdaOraclePrograms` supplies the canonical closed-lambda-term definition,
finite beta/query derivations, and continuity on arbitrary name domains.
`LambdaRealizers` attaches that definition to represented spaces;
`RepresentedProducts` and `LambdaProducts` construct product representations
and prove their computational universal property with explicit lambda terms. The older
`TypeTwoPrograms` and downstream modules are explicitly legacy oracle-recursive
results; they do not establish computability under the lambda definition.
Their constructions must be ported directly, starting with lambda combinators
for composition and numerical operations, rather than cross-model simulations.
The theorem below retains the reusable extensional core.
-/

namespace PolishSpaceBook

universe u v w t

open Function Set

section Realizers

variable {X : Type u} {Y : Type v} {Z : Type w}

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Let $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$ and $\PartialFunctionMap{\delta_Y}{\BaireSpace}{Y}$ be
    representations. A partial map
    $$\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$$
    \termdefineas{represented-space realization}{realizes} $f:X\to Y$ if
    $$\delta_Y(F(p))=f(\delta_X(p)) \qquad (p\in \DomainOf{\delta_X}).$$
    The function $f$ is:
-/
/-- Extensional realization, with partiality encoded by the representation domains. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For representations $\delta_X,\delta_Y$, a partial name map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ realizes
    $f:X\to Y$ when its domain contains $\DomainOf{\delta_X}$, its values there belong to $\DomainOf{\delta_Y}$, and
    $$\delta_Y(F(p))=f(\delta_X(p))\qquad(p\in\DomainOf{\delta_X}).$$
    The function $f$ is \termdefineas{computable function between represented spaces}{computable} if such an $F$ has a
    Type-Two lambda realizer. Thus $F$ is the map between names, and the closed lambda term is the program computing it. One
    program must work for every name of every input point.
-/
def Realizes (δX : Representation X) (δY : Representation Y)
    (F : δX.domain → δY.domain) (f : X → Y) : Prop :=
  ∀ p, δY.toFun (F p) = f (δX.toFun p)

/-- Existence of an extensional realizer. -/
def HasRealizer (δX : Representation X) (δY : Representation Y)
    (f : X → Y) : Prop :=
  ∃ F : δX.domain → δY.domain, Realizes δX δY F f

theorem realizes_id (δX : Representation X) :
    Realizes δX δX id id := by
  intro p
  rfl

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **Composition.** Realizers compose. If $F$ realizes $f:\mathbf X\to\mathbf Y$ and $G$ realizes
    $g:\mathbf Y\to\mathbf Z$, then $G\circ F$ realizes $g\circ f$, because
    $$
    \delta_Z(G(F(p)))
    =g(\delta_Y(F(p)))
    =g(f(\delta_X(p))).
    $$
-/
theorem Realizes.comp {δX : Representation X} {δY : Representation Y}
    {δZ : Representation Z} {F : δX.domain → δY.domain}
    {G : δY.domain → δZ.domain} {f : X → Y} {g : Y → Z}
    (hG : Realizes δY δZ G g) (hF : Realizes δX δY F f) :
    Realizes δX δZ (G ∘ F) (g ∘ f) := by
  intro p
  rw [Function.comp_apply, hG, hF, Function.comp_apply]

section Products

variable {δZ : Representation Z} {δX : Representation X}
  {δY : Representation Y} {δXY : Representation (X × Y)}
  (leftName : δXY.domain → δX.domain)
  (rightName : δXY.domain → δY.domain)
  (pairName : δX.domain → δY.domain → δXY.domain)
  (left_spec : ∀ p, δX.toFun (leftName p) = (δXY.toFun p).1)
  (right_spec : ∀ p, δY.toFun (rightName p) = (δXY.toFun p).2)
  (pair_spec : ∀ p q, δXY.toFun (pairName p q) = (δX.toFun p, δY.toFun q))

include leftName rightName pairName left_spec right_spec pair_spec

/-- The extensional realizer algebra underlying the product criterion. -/
theorem hasRealizer_prod_iff (h : Z → X × Y) :
    HasRealizer δZ δXY h ↔
      HasRealizer δZ δX (Prod.fst ∘ h) ∧
      HasRealizer δZ δY (Prod.snd ∘ h) := by
  constructor
  · rintro ⟨H, hH⟩
    constructor
    · refine ⟨leftName ∘ H, ?_⟩
      intro p
      rw [Function.comp_apply, left_spec, hH, Function.comp_apply]
    · refine ⟨rightName ∘ H, ?_⟩
      intro p
      rw [Function.comp_apply, right_spec, hH, Function.comp_apply]
  · rintro ⟨⟨HX, hHX⟩, ⟨HY, hHY⟩⟩
    refine ⟨fun p ↦ pairName (HX p) (HY p), ?_⟩
    intro p
    rw [pair_spec, hHX, hHY]
    rfl

end Products

end Realizers

section MetricMargins

variable {M : Type u} [MetricSpace M]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **Basic opens.** A rational ball $\Ball{q_i}{r}$ is effectively open because from a Cauchy name $p$ for $x$ one can
    search for $n$ with
    $$
    d(q_{p(n)},q_i)+2^{-n}<r.
    $$
    If such an $n$ is found, then $x\in \Ball{q_i}{r}$.
-/
theorem mem_ball_of_approximation {x a c : M} {ε r : ℝ}
    (hxa : dist x a ≤ ε) (hac : dist a c + ε < r) :
    x ∈ Metric.ball c r := by
  rw [Metric.mem_ball]
  calc
    dist x c ≤ dist x a + dist a c := dist_triangle _ _ _
    _ ≤ ε + dist a c := add_le_add hxa le_rfl
    _ = dist a c + ε := add_comm _ _
    _ < r := hac

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Then $d(q_{j_n},y)<2^{-(n+2)}$, so for $m\ge n$ the triangle inequality gives
    $$
    d(q_{j_n},q_{j_m})
    <2^{-(n+2)}+2^{-(m+2)}
    \le 2^{-(n+1)}
    \le 2^{-n}.
    $$
    Thus $\Sequence{q_{j_n}}{n\in\omega}$ is a fast Cauchy sequence, and the same estimates show that it converges to $y$.
-/
theorem fastCauchy_of_close {a : ℕ → M} {y : M}
    (ha : ∀ n, dist (a n) y < (1 / 2 : ℝ) ^ (n + 2)) :
    ∀ n m, n ≤ m → dist (a n) (a m) ≤ (1 / 2 : ℝ) ^ n := by
  intro n m hnm
  apply le_of_lt
  have hpow : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ (n + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hnm 2)
  calc
    dist (a n) (a m) ≤ dist (a n) y + dist y (a m) := dist_triangle _ _ _
    _ = dist (a n) y + dist (a m) y := by rw [dist_comm y (a m)]
    _ < (1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (m + 2) :=
      add_lt_add (ha n) (ha m)
    _ ≤ (1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (n + 2) :=
      add_le_add le_rfl hpow
    _ = (1 / 2 : ℝ) ^ (n + 1) := by ring
    _ ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)

end MetricMargins

section Randomness

variable {Ω : Type u}

/-- Avoidance of the intersection coded by a sequence of sets. -/
def AvoidsTest (x : Ω) (U : ℕ → Set Ω) : Prop :=
  x ∉ ⋂ n, U n

/-- An abstract Martin-Löf test: effectivity and mass are supplied as parameters. -/
def MartinLofTest (UniformlyEffectivelyOpen : (ℕ → Set Ω) → Prop)
    (mass : Set Ω → ℝ) (U : ℕ → Set Ω) : Prop :=
  UniformlyEffectivelyOpen U ∧ ∀ n, mass (U n) ≤ (1 / 2 : ℝ) ^ n

def MartinLofRandom (UniformlyEffectivelyOpen : (ℕ → Set Ω) → Prop)
    (mass : Set Ω → ℝ) (x : Ω) : Prop :=
  ∀ U, MartinLofTest UniformlyEffectivelyOpen mass U → AvoidsTest x U

/-- An abstract effective null `G_delta` test, without a prescribed rate. -/
def WeakTwoTest (UniformlyEffectivelyOpen : (ℕ → Set Ω) → Prop)
    (IsNull : Set Ω → Prop) (U : ℕ → Set Ω) : Prop :=
  UniformlyEffectivelyOpen U ∧ IsNull (⋂ n, U n)

/-- Avoidance of every abstract effective null `G_delta` test. -/
def WeakTwoRandom (UniformlyEffectivelyOpen : (ℕ → Set Ω) → Prop)
    (IsNull : Set Ω → Prop) (x : Ω) : Prop :=
  ∀ U, WeakTwoTest UniformlyEffectivelyOpen IsNull U → AvoidsTest x U

/-- Weak 2-randomness implies Martin-Löf randomness whenever every bounded
Martin-Löf test has null intersection. Strictness is not formalized here. -/
theorem WeakTwoRandom.martinLofRandom
    {UniformlyEffectivelyOpen : (ℕ → Set Ω) → Prop} {mass : Set Ω → ℝ}
    {IsNull : Set Ω → Prop} {x : Ω}
    (hNull : ∀ U, MartinLofTest UniformlyEffectivelyOpen mass U →
      IsNull (⋂ n, U n))
    (hx : WeakTwoRandom UniformlyEffectivelyOpen IsNull x) :
    MartinLofRandom UniformlyEffectivelyOpen mass x := by
  intro U hU
  exact hx U ⟨hU.1, hNull U hU⟩

end Randomness

section Weihrauch

/-- A partial multivalued problem, with empty values outside its domain. -/
def MultiProblem (X : Type u) (Y : Type v) := X → Set Y

namespace MultiProblem

variable {X : Type u} {Y : Type v}

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    A \termdefineas{Weihrauch problem}{problem} from $\mathbf X$ to $\mathbf Y$ is specified by a domain
    $\DomainOf{F}\IncludedIn X$ and a nonempty set $F(x)\IncludedIn Y$ of admissible solutions for every
    $x\in\DomainOf{F}$.
-/
def domain (F : MultiProblem X Y) : Set X :=
  {x | (F x).Nonempty}

end MultiProblem

/-- A partial operator on Baire-space names. -/
abbrev PartialNameMap := baire_space → Option baire_space

/-- A multivalued problem already lifted to names. -/
abbrev NameProblem := MultiProblem baire_space baire_space

namespace NameProblem


def IsRealizer (F : NameProblem) (Φ : PartialNameMap) : Prop :=
  ∀ p, (F p).Nonempty → ∃ q, Φ p = some q ∧ q ∈ F p

end NameProblem

/-- Ordinary postprocessing retains the original input through a pairing code. -/
def ordinaryWeihrauchPostprocess
    (pair : baire_space → baire_space → baire_space)
    (K H Γ : PartialNameMap) : PartialNameMap :=
  fun p ↦ do
    let k ← K p
    let answer ← Γ k
    H (pair p answer)


/-- Name-level Weihrauch reducibility relative to an external computability
predicate and a fixed pairing of Baire names. -/
def WeihrauchReduces
    (IsComputable : PartialNameMap → Prop)
    (pair : baire_space → baire_space → baire_space)
    (F G : NameProblem) : Prop :=
  ∃ K H, IsComputable K ∧ IsComputable H ∧
    ∀ Γ, G.IsRealizer Γ →
      F.IsRealizer (ordinaryWeihrauchPostprocess pair K H Γ)

/-- Strong postprocessing sees only the oracle answer. -/
def strongWeihrauchPostprocess (K H Γ : PartialNameMap) : PartialNameMap :=
  fun p ↦ do
    let k ← K p
    let answer ← Γ k
    H answer


def StrongWeihrauchReduces
    (IsComputable : PartialNameMap → Prop) (F G : NameProblem) : Prop :=
  ∃ K H, IsComputable K ∧ IsComputable H ∧
    ∀ Γ, G.IsRealizer Γ →
      F.IsRealizer (strongWeihrauchPostprocess K H Γ)

end Weihrauch

end PolishSpaceBook
