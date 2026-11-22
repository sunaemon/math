module

public import PolishSpaceBook.TriposToposForcingRealizability

@[expose] public section

/-!
# Inside the effective topos

Formalization targets for `polish-space/src/polish-space-book/inside-effective-topos.md`.

The pointwise PER calculation and metric core of doubling are proved here.
`LambdaAssemblies` supplies the assembly category and fully faithful embedding;
`LambdaComputablePointAssemblies` supplies total lambda index transformations and
the induced morphisms on computable-point assemblies. `LambdaRealDoubling` adds
the rational-code program, literal name transformer, total index transformation,
and four tracked relation conditions for doubling. `LambdaAssemblyProducts`
constructs assembly products and their comparison with paired-name representations;
`LambdaRealAddition` implements addition on Cauchy names and compiles a total
tracker on pairs of indices. Imported internal principles and the remaining
analytic constructions retain explicit source boundaries.
-/

namespace PolishSpaceBook

open Filter Set Topology

universe u v

section AssemblyPER

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    An \termforward{assembly} $A=(|A|,\Vdash_A)$ assigns a nonempty set
    $E_A(x):=\{e:e\Vdash_A x\}\IncludedIn\NN$ to each $x\in|A|$. A morphism $f:A\to B$ is a function on the
    underlying sets for which one index $r$ satisfies
    $$e\in E_A(x)\quad\Longrightarrow\quad r\cdot e\text{ is defined and belongs to }E_B(f(x)).$$
    Only the function is part of the morphism; the tracker is required to exist. Identity and composition of functions
    are tracked by the identity program and composition of the two tracking programs. This gives the category of assemblies.
    The associated realizer-valued relation is
    $$
    x\sim_A y=
    \begin{cases}
    E_A(x), & x=y,\\
    \emptyset, & x\ne y.
    \end{cases}
    $$
-/
/-- The set-valued PER associated with an assembly realization relation. -/
def assemblyPER {R : Type u} {A : Type v} (Realizes : R → A → Prop)
    (x y : A) : Set R :=
  {e | x = y ∧ Realizes e x}

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: Assembly PER calculation
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    If $e$ realizes $x\sim_A y$, then $x=y$, so the same $e$ realizes $y\sim_A x$. If $e$ realizes $x\sim_A y$ and $e'$
    realizes $y\sim_A z$, then $x=y=z$, so $e$ realizes $x\sim_A z$.
    \end{proof}
-/
theorem assemblyPER_symmetric_transitive
    {R : Type u} {A : Type v} (Realizes : R → A → Prop) :
    (∀ x y e, e ∈ assemblyPER Realizes x y →
      e ∈ assemblyPER Realizes y x) ∧
    (∀ x y z e e', e ∈ assemblyPER Realizes x y →
      e' ∈ assemblyPER Realizes y z → e ∈ assemblyPER Realizes x z) := by
  constructor
  · rintro x y e ⟨rfl, he⟩
    exact ⟨rfl, he⟩
  · rintro x y z e e' ⟨rfl, he⟩ ⟨rfl, _he'⟩
    exact ⟨rfl, he⟩

end AssemblyPER

section DoublingCauchyNames

/-- Shift a name by one coordinate and apply the basic-point doubling map. -/
def shiftedDoubleName (dbl : ℕ → ℕ) (p : baire_space) : baire_space :=
  fun n ↦ dbl (p (n + 1))

theorem shiftedDoubleName_isCauchyName
    (q : ℕ → ℝ) (dbl : ℕ → ℕ)
    (hDouble : ∀ i, q (dbl i) = 2 * q i)
    {p : baire_space} (hp : IsCauchyName q p) :
    IsCauchyName q (shiftedDoubleName dbl p) := by
  intro n m hnm
  have hp' := hp (n + 1) (m + 1) (Nat.add_le_add_right hnm 1)
  calc
    dist (q (shiftedDoubleName dbl p n))
          (q (shiftedDoubleName dbl p m)) =
        dist (2 * q (p (n + 1))) (2 * q (p (m + 1))) := by
          rw [shiftedDoubleName, shiftedDoubleName, hDouble, hDouble]
    _ ≤ ‖(2 : ℝ)‖ * dist (q (p (n + 1))) (q (p (m + 1))) := by
      simpa only [smul_eq_mul] using
        (dist_smul_le (2 : ℝ) (q (p (n + 1))) (q (p (m + 1))))
    _ ≤ 2 * (1 / 2 : ℝ) ^ (n + 1) := by
      norm_num
      exact hp'
    _ = (1 / 2 : ℝ) ^ n := by ring

theorem tendsto_shiftedDoubleName
    (q : ℕ → ℝ) (dbl : ℕ → ℕ)
    (hDouble : ∀ i, q (dbl i) = 2 * q i)
    {p : baire_space} {x : ℝ}
    (hp : Tendsto (fun n ↦ q (p n)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ q (shiftedDoubleName dbl p n)) atTop (𝓝 (2 * x)) := by
  have hshift : Tendsto (fun n ↦ q (p (n + 1))) atTop (𝓝 x) :=
    hp.comp (Filter.tendsto_add_atTop_nat 1)
  have hscaled :
      Tendsto (fun n ↦ (2 : ℝ) * q (p (n + 1))) atTop (𝓝 ((2 : ℝ) * x)) :=
    tendsto_const_nhds.mul hshift
  simpa [shiftedDoubleName, hDouble] using hscaled

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: Shifted doubling preserves Cauchy names
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $m\ge n$, the pairwise Cauchy-name bound gives
    $$
    \begin{aligned}
    d(q_{\psi_e(n)},q_{\psi_e(m)})
    &\le 2d(q_{\varphi_e(n+1)},q_{\varphi_e(m+1)})\\
    &\le 2\cdot 2^{-(n+1)}=2^{-n}.
    \end{aligned}
    $$
    Thus $\psi_e$ satisfies the defining pairwise condition for $\DomainOf{\rho_{\R}}$. Moreover,
    $q_{\varphi_e(n+1)}\to x$, so $q_{\psi_e(n)}=2q_{\varphi_e(n+1)}\to2x$. Hence $\rho_{\R}(\psi_e)=2x$.
    \end{proof}
-/
theorem shiftedDoubleName_correct
    (q : ℕ → ℝ) (dbl : ℕ → ℕ)
    (hDouble : ∀ i, q (dbl i) = 2 * q i)
    {p : baire_space} {x : ℝ}
    (hpName : IsCauchyName q p)
    (hpLimit : Tendsto (fun n ↦ q (p n)) atTop (𝓝 x)) :
    IsCauchyName q (shiftedDoubleName dbl p) ∧
      Tendsto (fun n ↦ q (shiftedDoubleName dbl p n)) atTop (𝓝 (2 * x)) :=
  ⟨shiftedDoubleName_isCauchyName q dbl hDouble hpName,
    tendsto_shiftedDoubleName q dbl hDouble hpLimit⟩

end DoublingCauchyNames

end PolishSpaceBook
