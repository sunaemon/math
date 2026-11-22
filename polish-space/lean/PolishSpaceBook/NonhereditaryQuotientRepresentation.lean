module

public import PolishSpaceBook.RepresentedSubspaceTopology

@[expose] public section

/-!
# A quotient representation whose restriction has a finer topology

Two tagged convergent sequences force any open neighborhood of c to contain
b, then a. After restricting to {a,c}, the first coordinate separates their
names, so the name-induced topology separates c although the subspace does not.
-/
namespace PolishSpaceBook.SubspaceCounterexample
open Set Function Filter Topology
open scoped OnePoint

inductive Point where
  | a | b | c
  deriving DecidableEq
open Point

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{samepage}
    Put $X=\{a,b,c\}$ and, for $p\in\BaireSpace$, write $P(p)$ for $\exists n\;p(n+1)\ne0$. Define
    $$
    \delta(p)=
    \begin{cases}
    a & p(0)=0,\ P(p),\\
    b & p(0)=0,\ \neg P(p),\\
    b & p(0)\ne0,\ P(p),\\
    c & p(0)\ne0,\ \neg P(p).
    \end{cases}
    $$
    \end{samepage}
    Zero and nonzero tails with initial tags zero and one supply names of all three points. Give $X$ the quotient topology induced by $\delta$, so a set is open exactly when its preimage is open in $\BaireSpace$.
-/
noncomputable def value (p : baire_space) : Point := by
  classical
  exact if p 0 = 0 then (if ∃ n, p (n+1) ≠ 0 then a else b)
    else (if ∃ n, p (n+1) ≠ 0 then b else c)

noncomputable def representation : Representation Point where
  domain := univ
  toFun p := value p.val
  surjective := by
    intro x
    cases x with
    | a => exact ⟨⟨prefixName 0 (fun _ => 1), mem_univ _⟩, by simp [value, prefixName]⟩
    | b => exact ⟨⟨prefixName 0 (fun _ => 0), mem_univ _⟩, by simp [value, prefixName]⟩
    | c => exact ⟨⟨prefixName 1 (fun _ => 0), mem_univ _⟩, by simp [value, prefixName]⟩

noncomputable instance : TopologicalSpace Point := TopologicalSpace.coinduced representation.toFun inferInstance

theorem representation_isQuotientMap : IsQuotientMap representation.toFun :=
  ⟨⟨rfl⟩, representation.surjective⟩

noncomputable def sequenceName (tag : ℕ) (z : OnePoint ℕ) : representation.domain :=
  ⟨prefixName tag (convergentSequenceName z), mem_univ _⟩

theorem continuous_sequenceName (tag : ℕ) : Continuous (sequenceName tag) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  cases k with
  | zero => exact continuous_const
  | succ n => exact (continuous_apply n).comp continuous_convergentSequenceName

@[simp] theorem value_sequenceName_zero_nat (n : ℕ) :
    representation.toFun (sequenceName 0 (n : OnePoint ℕ)) = a := by
  have h : ∃ k, convergentSequenceName (n : OnePoint ℕ) k ≠ 0 :=
    ⟨n, by simp [convergentSequenceName]⟩
  simp [representation, sequenceName, value, prefixName, h]

@[simp] theorem value_sequenceName_one_nat (n : ℕ) :
    representation.toFun (sequenceName 1 (n : OnePoint ℕ)) = b := by
  have h : ∃ k, convergentSequenceName (n : OnePoint ℕ) k ≠ 0 :=
    ⟨n, by simp [convergentSequenceName]⟩
  simp [representation, sequenceName, value, prefixName, h]

@[simp] theorem value_sequenceName_zero_infty :
    representation.toFun (sequenceName 0 ∞) = b := by
  simp [representation, sequenceName, value, prefixName, convergentSequenceName]

@[simp] theorem value_sequenceName_one_infty :
    representation.toFun (sequenceName 1 ∞) = c := by
  simp [representation, sequenceName, value, prefixName, convergentSequenceName]

/-- Every open neighborhood of b contains a, and every one of c contains b. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Use the names $e_n,e_\infty$ from the preceding proof. Prefixing a fixed tag is continuous, and
    $$
    \begin{aligned}
    \delta(\langle0\rangle\concat e_n)&=a,
    &\delta(\langle0\rangle\concat e_\infty)&=b,\\
    \delta(\langle1\rangle\concat e_n)&=b,
    &\delta(\langle1\rangle\concat e_\infty)&=c.
    \end{aligned}
    $$
    Since $\delta$ is continuous, every open neighborhood of $b$ contains $a$, and every open neighborhood of $c$ contains $b$. Consequently every open neighborhood of $c$ contains $a$. In the subspace $A=\{a,c\}$, the set $\{c\}$ is therefore not open.
-/
theorem open_contains_predecessors {V : Set Point} (hV : IsOpen V) :
    (b ∈ V → a ∈ V) ∧ (c ∈ V → b ∈ V) := by
  have ht : Tendsto (fun n : ℕ => (n : OnePoint ℕ)) atTop (𝓝 ∞) :=
    (OnePoint.continuous_iff_from_nat id).mp continuous_id
  have hlim (tag : ℕ) :=
    (representation_isQuotientMap.continuous.comp (continuous_sequenceName tag)).tendsto ∞ |>.comp ht
  constructor
  · intro hb
    have he := (hlim 0).eventually (hV.mem_nhds (by simpa using hb))
    obtain ⟨n, hn⟩ := he.exists
    change V a
    simpa only [Function.comp_apply, value_sequenceName_zero_nat] using hn
  · intro hc
    have he := (hlim 1).eventually (hV.mem_nhds (by simpa using hc))
    obtain ⟨n, hn⟩ := he.exists
    change V b
    simpa only [Function.comp_apply, value_sequenceName_one_nat] using hn

def retained : Set Point := {x | x = a ∨ x = c}
def separated : Set retained := {x | x.val = c}

/-- In the ordinary subspace topology, {c} is not open. -/
theorem not_isOpen_separated : ¬ IsOpen separated := by
  intro h
  obtain ⟨V,hV,heq⟩ := isOpen_induced_iff.mp h
  have hc : c ∈ V := by
    have hm : (⟨c,Or.inr rfl⟩ : retained) ∈ separated := rfl
    rw [← heq] at hm
    exact hm
  have ha : a ∈ V := (open_contains_predecessors hV).1 ((open_contains_predecessors hV).2 hc)
  have hm : (⟨a,Or.inl rfl⟩ : retained) ∈ separated := by
    rw [← heq]
    exact ha
  change a = c at hm
  cases hm

/-- On the restricted name domain, a nonzero tag recognizes exactly the names of c. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    On the restricted name domain, however, a name has value $c$ exactly when its initial coordinate is nonzero: the alternative value $b$ has been excluded. Hence
    $$\delta_A^{-1}(\{c\})=\{p\in\DomainOf{\delta_A}:p(0)\ne0\}$$
    is relatively open, since the zeroth-coordinate projection is continuous and the naturals are discrete. Thus $\{c\}$ is open for the restricted representation's induced topology. Continuity of the restriction ensures that all ordinary subspace opens remain open for that induced topology, so the inclusion of topologies is strict.
-/
theorem isOpen_preimage_separated :
    IsOpen ((restrictedRepresentation representation retained).toFun ⁻¹' separated) := by
  classical
  have heq : (restrictedRepresentation representation retained).toFun ⁻¹' separated =
      {p : (restrictedRepresentation representation retained).domain | p.val 0 ≠ 0} := by
    ext p
    change value p.val = c ↔ p.val 0 ≠ 0
    have hp : value p.val = a ∨ value p.val = c := p.property.choose_spec
    unfold value at hp ⊢
    split_ifs at hp ⊢ <;> simp_all
  rw [heq]
  exact isOpen_ne.preimage ((continuous_apply 0).comp continuous_subtype_val)

/-- The original quotient property does not survive this represented-subspace restriction. -/
theorem restriction_not_quotient :
    ¬ IsQuotientMap (restrictedRepresentation representation retained).toFun := by
  intro h
  exact not_isOpen_separated (h.isOpen_preimage.mp isOpen_preimage_separated)

/-- One explicit witness to the failure of topology recovery after restriction. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: example
  title: Failure of quotient-map restriction
-/
theorem counterexample : IsQuotientMap representation.toFun ∧
    ¬ IsOpen separated ∧
    IsOpen ((restrictedRepresentation representation retained).toFun ⁻¹' separated) :=
  ⟨representation_isQuotientMap, not_isOpen_separated, isOpen_preimage_separated⟩

end PolishSpaceBook.SubspaceCounterexample
