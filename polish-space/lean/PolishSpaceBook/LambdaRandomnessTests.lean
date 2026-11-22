module

public import PolishSpaceBook.ComputablePolishSpacesTTE
public import PolishSpaceBook.LambdaMeasureBounds
public import PolishSpaceBook.LambdaListTabulation

@[expose] public section

/-! # Randomness tests with actual numerical lambda enumerations

The two arguments of an open family are encoded together. Computable measures
in a Schnorr test likewise use a single numerical program on (row,precision).
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- One program enumerates all rows; each entry is padding or a binary cylinder. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Here uniform effective openness means that one closed numerical lambda term $P$ computes a table
    $p(\NatPair{n}{s})$ of valid cylinder entries, with
    $$U_n=\bigcup_s V_{p(\NatPair{n}{s})}.$$
    Both the row $n$ and the enumeration stage $s$ are numerical inputs to the same program. The entry convention
    is that of §{sec:tte-cantor-open-measure}; in particular, empty stages and repetitions are allowed.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Martin-Löf randomness instead restricts the tests effectively:
    a test is a uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$, and a real
    passes it when
    it lies outside $\bigcap_n U_n$. The intersection is null; the individual open sets need not be null.
    A Martin-Löf random real passes every such test.
-/
def UniformlyOpen (U : ℕ → Set (ℕ → Bool)) : Prop :=
  ∃ P : AlphaTerm, ∃ p : ℕ → ℕ, NumericalComputes P p ∧
    (∀ n, ValidOpenName (fun s => p (Nat.pair n s))) ∧
    ∀ n, U n = namedOpen (fun s => p (Nat.pair n s))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Martin-Löf randomness instead restricts the tests effectively:
    a test is a uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$, and a real
    passes it when
    it lies outside $\bigcap_n U_n$. The intersection is null; the individual open sets need not be null.
    A Martin-Löf random real passes every such test.
-/
abbrev MLTest := MartinLofTest UniformlyOpen fairCoinProduct.real
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Martin-Löf randomness instead restricts the tests effectively:
    a test is a uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$, and a real
    passes it when
    it lies outside $\bigcap_n U_n$. The intersection is null; the individual open sets need not be null.
    A Martin-Löf random real passes every such test.
-/
abbrev MLRandom := MartinLofRandom UniformlyOpen fairCoinProduct.real
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
abbrev W2Test := WeakTwoTest UniformlyOpen (fun S => fairCoinProduct S = 0)
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
abbrev W2Random := WeakTwoRandom UniformlyOpen (fun S => fairCoinProduct S = 0)

/-- Precision and test row both remain inputs of the same closed program. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    In the Schnorr condition, uniform computability of the measures means that there are fast Cauchy names $q_n$
    of $\mu(U_n)$ and one closed numerical term $M$ satisfying
    $$M\ChurchNumeral{\NatPair{n}{k}}\to_\beta^*\ChurchNumeral{q_n(k)}.$$
    The precision $k$ is an input, as is the test row $n$. We now work with the fair-coin measure on Cantor space.
-/
def UniformComputableMass (U : ℕ → Set (ℕ → Bool)) : Prop :=
  ∃ P : AlphaTerm, ∃ p : ℕ → realRepresentation.domain,
    NumericalComputes P (fun z => (p z.unpair.1).val z.unpair.2) ∧
    ∀ n, realRepresentation.toFun (p n) = fairCoinProduct.real (U n)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    \termdefine{Schnorr randomness} tightens the measure side of the test [@Schnorr1971]. A \termdefine{Schnorr test} is a
    Martin-Löf test $\Sequence{U_n}{n\in\omega}$ for which the real number $\mu(U_n)$ is computable uniformly in $n$. Every
    Martin-Löf random
    point is Schnorr random. The converse fails already for fair-coin measure on Cantor space. The distinction
    matters because Schnorr randomness treats the measure of
    the test itself as part of the effective data, matching the computable-analysis principle that negative information
    should be supplied with a usable modulus rather than only an existence proof.
-/
def SchnorrTest (U : ℕ → Set (ℕ → Bool)) : Prop := MLTest U ∧ UniformComputableMass U

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    \termdefine{Schnorr randomness} tightens the measure side of the test [@Schnorr1971]. A \termdefine{Schnorr test} is a
    Martin-Löf test $\Sequence{U_n}{n\in\omega}$ for which the real number $\mu(U_n)$ is computable uniformly in $n$. Every
    Martin-Löf random
    point is Schnorr random. The converse fails already for fair-coin measure on Cantor space. The distinction
    matters because Schnorr randomness treats the measure of
    the test itself as part of the effective data, matching the computable-analysis principle that negative information
    should be supplied with a usable modulus rather than only an existence proof.
-/
def SchnorrRandom (x : ℕ → Bool) : Prop := ∀ U, SchnorrTest U → AvoidsTest x U

theorem UniformlyOpen.isOpen {U : ℕ → Set (ℕ → Bool)} (h : UniformlyOpen U) (n : ℕ) :
    IsOpen (U n) := by
  obtain ⟨_,p,_,_,he⟩ := h
  rw [he n]
  exact isOpen_namedOpen (fun s => p (Nat.pair n s))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Implications between randomness notions
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For a Martin-Löf test, monotonicity of the measure gives
    $$0\le\mu\left(\bigcap_m U_m\right)\le\mu(U_n)\le 2^{-n}\qquad(n\in\NN).$$
    Letting $n$ tend to infinity shows that the intersection is null. The same enumeration is therefore a weak
    2-randomness test, so avoiding all such tests implies avoidance of every Martin-Löf test. A Schnorr test
    already is a Martin-Löf test, which proves the second implication.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Martin-Löf randomness instead restricts the tests effectively:
    a test is a uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$, and a real
    passes it when
    it lies outside $\bigcap_n U_n$. The intersection is null; the individual open sets need not be null.
    A Martin-Löf random real passes every such test.
-/
theorem MLTest.null_intersection {U : ℕ → Set (ℕ → Bool)} (h : MLTest U) :
    fairCoinProduct (⋂ n, U n) = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ (measureReal_nonneg)
  have ht : Tendsto (fun n => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact ge_of_tendsto ht (Eventually.of_forall (fun n =>
    (measureReal_mono (μ := fairCoinProduct) (iInter_subset U n)).trans (h.2 n)))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Implications between randomness notions
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
theorem W2Random.mlRandom {x : ℕ → Bool} (h : W2Random x) : MLRandom x :=
  WeakTwoRandom.martinLofRandom (fun _ ht => MLTest.null_intersection ht) h

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Implications between randomness notions
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    \termdefine{Schnorr randomness} tightens the measure side of the test [@Schnorr1971]. A \termdefine{Schnorr test} is a
    Martin-Löf test $\Sequence{U_n}{n\in\omega}$ for which the real number $\mu(U_n)$ is computable uniformly in $n$. Every
    Martin-Löf random
    point is Schnorr random. The converse fails already for fair-coin measure on Cantor space. The distinction
    matters because Schnorr randomness treats the measure of
    the test itself as part of the effective data, matching the computable-analysis principle that negative information
    should be supplied with a usable modulus rather than only an existence proof.
-/
theorem MLRandom.schnorrRandom {x : ℕ → Bool} (h : MLRandom x) : SchnorrRandom x :=
  fun U hU => h U hU.1

/-- A pointwise approximation is eventual equality at each binary coordinate.
No uniform stage of stabilization is assumed. -/
def Approximates (a : ℕ → ℕ → Bool) (x : ℕ → Bool) : Prop :=
  ∀ k, ∃ N, ∀ s ≥ N, a s k = x k

def approxWord (a : ℕ → ℕ → Bool) (s n : ℕ) : List Bool := (List.range n).map (a s)

theorem mem_approxWord_cyl (a : ℕ → ℕ → Bool) (s n : ℕ) (y : ℕ → Bool) :
    y ∈ cyl (approxWord a s n) ↔ ∀ k < n, y k = a s k := by
  simp [cyl,prefixOfSeq,approxWord]

def limitOpen (a : ℕ → ℕ → Bool) (n : ℕ) : Set (ℕ → Bool) :=
  ⋃ t, cyl (approxWord a (n+t) n)

def limitOpenName (a : ℕ → ℕ → Bool) (z : ℕ) : ℕ :=
  encodeWord (approxWord a (z.unpair.1+z.unpair.2) z.unpair.1) + 1

/-- Prepare (stage,length), tabulate the given approximation, and tag the word. -/
def limitOpenProgram (A : AlphaTerm) : AlphaTerm :=
  numericalCompose successorTerm (numericalCompose (listTabulateTerm A)
    (pairNumerical (addNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))
      (numericalProjectionTerm true)))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: A null test for a computable limit approximation
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Set
    $$W_n:=\bigcup_{t\in\NN}\cyl{\restrict{a_{n+t}}{n}}.$$
    Let $A$ be the term computing the bits. The finite-tabulation routine preserves the stage parameter and
    returns the first $n$ bits in order. Thus the following closed term computes a cylinder-entry table for $W_n$:
    $$\begin{aligned}
    H&:=\lambdaab{z}{\LambdaAdd\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)},\\
    J&:=\lambdaab{z}{\LambdaNumericPair\,(Hz)\,(\LambdaNumericProjection{1}z)},\\
    P&:=\lambdaab{z}{\LambdaSucc\,(\LambdaListTabulate{A}(Jz))}.
    \end{aligned}$$
    On input $\NatPair{n}{t}$, it returns the code of $\restrict{a_{n+t}}{n}$ plus one. This is a valid entry because
    all the tabulated values are bits. Every calculation terminates; the program never waits for a coordinate to
    stabilize.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For each fixed $n$, the first $n$ coordinates eventually all agree with $x$, so $x\in W_n$.
    Conversely, suppose $y\in\bigcap_n W_n$ and fix a coordinate $k$. Choose $N$ so that $a_s(k)=x(k)$ for
    all $s\ge N$, and take $n\ge\max\{N,k+1\}$. Membership in $W_n$ supplies a $t$ with
    $y\in\cyl{\restrict{a_{n+t}}{n}}$, hence
    $$y(k)=a_{n+t}(k)=x(k).$$
    This holds at every coordinate, proving $\bigcap_n W_n=\{x\}$. Singletons have fair-coin measure zero by
    §{sec:random-forcing-detail}. Thus this is a weak 2-randomness test covering $x$.
-/
theorem limitOpenProgram_computes {A : AlphaTerm} {a : ℕ → ℕ → Bool}
    (ha : NumericalComputes A (fun z => (a z.unpair.1 z.unpair.2).toNat)) :
    NumericalComputes (limitOpenProgram A) (limitOpenName a) := by
  have hn := ((projection_computes true).add (projection_computes false)).pair (projection_computes true)
  have ht := (listTabulate_computes ha).comp hn
  have h := successor_computes.comp ht
  refine ⟨h.1,fun z => ?_⟩
  simpa only [limitOpenProgram,limitOpenName,encodeWord,approxWord,List.map_map,Nat.unpair_pair,
    Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,Nat.succ_eq_add_one,Function.comp_def] using h.2 z

theorem limitOpenName_valid (a : ℕ → ℕ → Bool) (n : ℕ) :
    ValidOpenName (fun s => limitOpenName a (Nat.pair n s)) := by
  intro s
  apply Or.inr
  simpa only [limitOpenName,Nat.unpair_pair,Nat.add_sub_cancel] using binary_encodeWord (approxWord a (n+s) n)

theorem limitOpenName_names (a : ℕ → ℕ → Bool) (n : ℕ) :
    limitOpen a n = namedOpen (fun s => limitOpenName a (Nat.pair n s)) := by
  simp [limitOpen,namedOpen,limitOpenName,entrySet]

theorem limitOpen_uniform {A : AlphaTerm} {a : ℕ → ℕ → Bool}
    (ha : NumericalComputes A (fun z => (a z.unpair.1 z.unpair.2).toNat)) :
    UniformlyOpen (limitOpen a) :=
  ⟨limitOpenProgram A,limitOpenName a,limitOpenProgram_computes ha,
    limitOpenName_valid a,limitOpenName_names a⟩

theorem Approximates.prefix_stable {a : ℕ → ℕ → Bool} {x : ℕ → Bool}
    (h : Approximates a x) (n : ℕ) : ∃ N, ∀ s ≥ N, ∀ k < n, a s k = x k := by
  induction n with
  | zero => exact ⟨0,fun _ _ k hk => by omega⟩
  | succ n ih =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨M,hM⟩ := h n
    refine ⟨max N M,fun s hs k hk => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkn | rfl
    · exact hN s (le_trans (le_max_left _ _) hs) k hkn
    · exact hM s (le_trans (le_max_right _ _) hs)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: A null test for a computable limit approximation
-/
theorem Approximates.intersection_eq_singleton {a : ℕ → ℕ → Bool} {x : ℕ → Bool}
    (h : Approximates a x) : (⋂ n, limitOpen a n) = {x} := by
  ext y
  constructor
  · intro hy
    apply mem_singleton_iff.mpr
    funext k
    obtain ⟨N,hN⟩ := h k
    obtain ⟨t,ht⟩ := mem_iUnion.mp (mem_iInter.mp hy (max N (k+1)))
    have he := (mem_approxWord_cyl a _ _ y).mp ht k (by omega)
    exact he.trans (hN _ (by omega))
  · rintro rfl
    apply mem_iInter.mpr
    intro n
    obtain ⟨N,hN⟩ := h.prefix_stable n
    apply mem_iUnion.mpr
    refine ⟨N,(mem_approxWord_cyl a _ _ y).mpr ?_⟩
    intro k hk
    exact (hN (n+N) (by omega) k hk).symm

/-- A uniform open null test catches the limit even without a computable convergence rate. -/
theorem limitOpen_weakTwoTest {A : AlphaTerm} {a : ℕ → ℕ → Bool} {x : ℕ → Bool}
    (ha : NumericalComputes A (fun z => (a z.unpair.1 z.unpair.2).toNat))
    (hx : Approximates a x) : W2Test (limitOpen a) := by
  refine ⟨limitOpen_uniform ha,?_⟩
  rw [hx.intersection_eq_singleton]
  exact measure_singleton x

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: A null test for a computable limit approximation
-/
theorem not_weakTwoRandom_of_approximation {A : AlphaTerm} {a : ℕ → ℕ → Bool} {x : ℕ → Bool}
    (ha : NumericalComputes A (fun z => (a z.unpair.1 z.unpair.2).toNat))
    (hx : Approximates a x) : ¬ W2Random x := by
  intro hr
  have h := hr (limitOpen a) (limitOpen_weakTwoTest ha hx)
  apply h
  rw [hx.intersection_eq_singleton]
  exact mem_singleton x

/-- A constant sequence of approximants gives the usual shrinking cylinders. -/
theorem constant_limitOpen (x : ℕ → Bool) (n : ℕ) :
    limitOpen (fun _ => x) n = cyl ((List.range n).map x) := by
  simp only [limitOpen,approxWord]
  exact iUnion_const _

theorem constant_limitOpen_measure (x : ℕ → Bool) (n : ℕ) :
    fairCoinProduct.real (limitOpen (fun _ => x) n) = (1/2:ℝ)^n := by
  rw [constant_limitOpen,measureReal_def,fairCoinProduct_cyl]
  simp

/-- The cylinder measures have one numerical Cauchy-name program on (row,precision). -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: Computable points are not Schnorr random
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For a computable point $x$, take the constant approximation $a_s=x$ in the preceding construction.
    A bit program for this approximation projects $k$ from $\NatPair{s}{k}$ and applies the given bit program
    for $x$. Now
    $$W_n=\cyl{\restrict{x}{n}},\qquad \mu(W_n)=2^{-n}.$$
    These measures have constant fast Cauchy names, computed uniformly by
    $$M:=\lambdaab{z}{\LambdaDyadic(\LambdaNumericProjection{1}z)}.$$
    The approximation precision is the second component of the input and is unused because the output is exact.
    Thus $\Sequence{W_n}{n\in\omega}$ is a Schnorr test, and its intersection contains $x$.
-/
theorem constant_limitOpen_computableMass (x : ℕ → Bool) :
    UniformComputableMass (limitOpen (fun _ => x)) := by
  have he (n k : ℕ) : dist (rationalPoint (RationalCode.dyadic n).natCode) ((1/2:ℝ)^n) ≤
      (1/2:ℝ)^(k+1) := by rw [rationalPoint_dyadic,dist_self]; positivity
  let p : ℕ → realRepresentation.domain := fun n =>
    ⟨fun _ => (RationalCode.dyadic n).natCode,isCauchyName_of_halfError_le (he n)⟩
  refine ⟨numericalCompose rationalDyadicTerm (numericalProjectionTerm true),p,?_,?_⟩
  · exact rationalDyadic_computes.comp (projection_computes true)
  · intro n
    rw [constant_limitOpen_measure]
    exact cauchyRepresentation_eq_of_halfError_le _ _ (he n)

theorem computablePoint_schnorrTest {X : AlphaTerm} {x : ℕ → Bool}
    (hx : NumericalComputes X (fun k => (x k).toNat)) :
    SchnorrTest (limitOpen (fun _ => x)) := by
  have ha := hx.comp (projection_computes false)
  refine ⟨⟨limitOpen_uniform ha,fun n => ?_⟩,constant_limitOpen_computableMass x⟩
  exact le_of_eq (constant_limitOpen_measure x n)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: Computable points are not Schnorr random
-/
theorem not_schnorrRandom_of_computable {X : AlphaTerm} {x : ℕ → Bool}
    (hx : NumericalComputes X (fun k => (x k).toNat)) : ¬ SchnorrRandom x := by
  intro hr
  have ha : Approximates (fun _ => x) x := fun _ => ⟨0,fun _ _ => rfl⟩
  apply hr _ (computablePoint_schnorrTest hx)
  rw [ha.intersection_eq_singleton]
  exact mem_singleton x

end PolishSpaceBook.LambdaRandomness
