module

public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-!
# Set-theoretic forcing names and their valuation

Names are actual ZFC sets of ordered pairs. Recursion follows the rank of the
first coordinate of each pair. Valuation is defined for any collection of
conditions; the check-name calculation only needs it to meet the forcing set.
No model-closure or generic-extension theorem is assumed in these calculations.
-/

noncomputable section
namespace PolishSpaceBook.ForcingNames
universe u
open ZFSet

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Use the usual ordered pair $\langle\sigma,p\rangle=\{\{\sigma\},\{\sigma,p\}\}$.
    If $\langle\sigma,p\rangle\in\tau$, then
    $$\sigma\in\{\sigma\}\in\langle\sigma,p\rangle\in\tau.$$
    Thus the rank of $\sigma$ is strictly smaller than that of $\tau$, so the recursion is well founded.
-/
lemma child_rank_lt {σ p τ : ZFSet.{u}} (h : pair σ p ∈ τ) : σ.rank < τ.rank := by
  have h₁ : σ ∈ ({σ} : ZFSet) := by simp
  have h₂ : ({σ} : ZFSet) ∈ pair σ p := by simp [pair]
  exact (rank_lt_of_mem h₁).trans ((rank_lt_of_mem h₂).trans (rank_lt_of_mem h))

lemma child_mem_doubleUnion {σ p τ : ZFSet.{u}} (h : pair σ p ∈ τ) :
    σ ∈ ZFSet.sUnion (ZFSet.sUnion τ) := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨{σ}, ZFSet.mem_sUnion.mpr ⟨pair σ p, h, ?_⟩, ?_⟩ <;> simp [pair]

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For a set $P$ of conditions, define the class of \termdefineas{P-name}{$P$-names} recursively:
    $$\tau \text{ is a } P\text{-name}
    \quad\Longleftrightarrow\quad
    \tau \IncludedIn \{\langle \sigma,p\rangle : \sigma \text{ is a } P\text{-name and } p \in P\}.$$
-/
/-- Every member is a pair whose first coordinate is an earlier name. -/
def IsName (P τ : ZFSet.{u}) : Prop :=
  (∀ z ∈ τ, ∃ σ p, z = pair σ p) ∧
  ∀ σ p, pair σ p ∈ τ → p ∈ P ∧ IsName P σ
termination_by τ.rank
 decreasing_by exact child_rank_lt ‹pair _ _ ∈ _›

lemma isName_iff (P τ : ZFSet.{u}) : IsName P τ ↔
    (∀ z ∈ τ, ∃ σ p, z = pair σ p) ∧
    ∀ σ p, pair σ p ∈ τ → p ∈ P ∧ IsName P σ := by rw [IsName]

lemma IsName.child {P τ σ p : ZFSet.{u}} (hτ : IsName P τ) (h : pair σ p ∈ τ) :
    IsName P σ := ((isName_iff P τ).mp hτ).2 σ p h |>.2

lemma IsName.condition {P τ σ p : ZFSet.{u}} (hτ : IsName P τ) (h : pair σ p ∈ τ) :
    p ∈ P := ((isName_iff P τ).mp hτ).2 σ p h |>.1

/-- Restrict to a set-sized family of first coordinates, retaining only active pairs. -/
abbrev ActiveChild (G : Set ZFSet.{u}) (τ : ZFSet.{u}) :=
  {σ : ZFSet.sUnion (ZFSet.sUnion τ) // ∃ p ∈ G, pair σ.val p ∈ τ}

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For $G\IncludedIn P$, the \termdefine{valuation} of a name is defined by the same rank recursion:
    $$\tau^G := \{\sigma^G : \exists p \in G,\; \langle \sigma,p\rangle \in \tau\}.$$
    The first coordinates occurring here form a subset of $\bigcup\bigcup\tau$, so Replacement makes the right-hand side
    a set.
-/
def valuation (G : Set ZFSet.{u}) (τ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun σ : ActiveChild G τ => valuation G σ.val.val)
termination_by τ.rank
 decreasing_by
  obtain ⟨p, _, hp⟩ := σ.property
  exact child_rank_lt hp

lemma valuation_eq (G : Set ZFSet.{u}) (τ : ZFSet.{u}) :
    valuation G τ = ZFSet.range (fun σ : ActiveChild G τ => valuation G σ.val.val) := by
  rw [valuation]

lemma mem_valuation (G : Set ZFSet.{u}) (τ x : ZFSet.{u}) :
    x ∈ valuation G τ ↔ ∃ σ p, p ∈ G ∧ pair σ p ∈ τ ∧ valuation G σ = x := by
  rw [valuation_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨σ, hx⟩
    obtain ⟨p, hp, hστ⟩ := σ.property
    exact ⟨σ.val.val, p, hp, hστ, hx⟩
  · rintro ⟨σ, p, hp, hστ, hx⟩
    exact ⟨⟨⟨σ, child_mem_doubleUnion hστ⟩, p, hp, hστ⟩, hx⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    This recursion determines the valuation uniquely: if two assignments satisfy the displayed equation,
    induction on the rank of $\tau$ makes them agree on each contributing $\sigma$, hence on $\tau$ by Extensionality.
-/
/-- The membership recursion determines the valuation uniquely. -/
theorem valuation_unique (G : Set ZFSet.{u}) (V : ZFSet.{u} → ZFSet.{u})
    (hV : ∀ τ x, x ∈ V τ ↔ ∃ σ p, p ∈ G ∧ pair σ p ∈ τ ∧ V σ = x)
    (τ : ZFSet.{u}) : V τ = valuation G τ := by
  apply ZFSet.ext
  intro x
  rw [hV, mem_valuation]
  constructor
  · rintro ⟨σ, p, hp, hστ, hx⟩
    exact ⟨σ, p, hp, hστ, (valuation_unique G V hV σ).symm.trans hx⟩
  · rintro ⟨σ, p, hp, hστ, hx⟩
    exact ⟨σ, p, hp, hστ, (valuation_unique G V hV σ).trans hx⟩
termination_by τ.rank
decreasing_by all_goals exact child_rank_lt hστ

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For any set $x$, its \termdefine{check name} is defined by membership recursion:
    $$\check{x} := \{\langle \check{y},p\rangle : y \in x,\; p \in P\}.$$
    We use this all-conditions convention below; it does not require a weakest condition.
    When $P$ has a weakest condition $1_P$, the usual alternative is
    $$\check{x} := \{\langle \check{y},1_P\rangle : y \in x\}.$$
-/
/-- The all-conditions convention works without adjoining a weakest condition. -/
def check (P x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun yp : x × P => pair (check P yp.1.val) yp.2.val)
termination_by x.rank
 decreasing_by exact rank_lt_of_mem yp.1.property

lemma check_eq (P x : ZFSet.{u}) :
    check P x = ZFSet.range (fun yp : x × P => pair (check P yp.1.val) yp.2.val) := by rw [check]

lemma mem_check (P x z : ZFSet.{u}) :
    z ∈ check P x ↔ ∃ y ∈ x, ∃ p ∈ P, z = pair (check P y) p := by
  rw [check_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y, p⟩, h⟩
    exact ⟨y.val, y.property, p.val, p.property, h.symm⟩
  · rintro ⟨y, hy, p, hp, h⟩
    exact ⟨⟨⟨y, hy⟩, ⟨p, hp⟩⟩, h.symm⟩

lemma pair_mem_check (P x σ p : ZFSet.{u}) :
    pair σ p ∈ check P x ↔ ∃ y ∈ x, σ = check P y ∧ p ∈ P := by
  rw [mem_check]
  constructor
  · rintro ⟨y, hy, q, hq, he⟩
    obtain ⟨heσ, hep⟩ := pair_inj.mp he
    exact ⟨y, hy, heσ, hep ▸ hq⟩
  · rintro ⟨y, hy, rfl, hp⟩
    exact ⟨y, hy, p, hp, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Membership induction shows that $\check{x}$ is a name, since its first coordinates are names $\check{y}$ with $y\in x$.
-/
lemma check_isName (P x : ZFSet.{u}) : IsName P (check P x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [isName_iff]
    constructor
    · intro z hz
      obtain ⟨y, _, p, _, he⟩ := (mem_check P x z).mp hz
      exact ⟨check P y, p, he⟩
    · intro σ p hp
      obtain ⟨y, hy, rfl, hpP⟩ := (pair_mem_check P x σ p).mp hp
      exact ⟨hpP, ih y hy⟩

/-- A restricted supply of check-name conditions still gives names for P. -/
lemma check_isName_of_subset {Q P : ZFSet.{u}} (hQP : Q ⊆ P) (x : ZFSet.{u}) :
    IsName P (check Q x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [isName_iff]
    constructor
    · intro z hz
      obtain ⟨y, _, p, _, he⟩ := (mem_check Q x z).mp hz
      exact ⟨check Q y, p, he⟩
    · intro σ p hp
      obtain ⟨y, hy, rfl, hpQ⟩ := (pair_mem_check Q x σ p).mp hp
      exact ⟨hQP hpQ, ih y hy⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Basic valuation calculations
-/

/-- Evaluation of check names needs only a condition common to G and P. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For its valuation, the same induction gives
    $$\check{x}^G=\{\check{y}^G:y\in x,\;\exists p\,(p\in G)\}=\{y:y\in x\}=x.$$
    Nonemptiness of $G$ is used in the middle equality.
-/
theorem valuation_check (P : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) (x : ZFSet.{u}) : valuation G (check P x) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [mem_valuation]
    constructor
    · rintro ⟨σ, p, _, hpair, hz⟩
      obtain ⟨y, hy, rfl, _⟩ := (pair_mem_check P x σ p).mp hpair
      rw [ih y hy] at hz
      exact hz ▸ hy
    · intro hz
      obtain ⟨p, hpG, hpP⟩ := hG
      exact ⟨check P z, p, hpG, (pair_mem_check P x _ p).mpr ⟨z, hz, rfl, hpP⟩, ih z hz⟩

/-- A family of ground-set labels, each activated by its attached condition. -/
def decisionName {ι : Type*} [Small.{u} ι] (P : ZFSet.{u})
    (label condition : ι → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i => pair (check P (label i)) (condition i))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Basic valuation calculations
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The name property of $\tau$ follows from that of the check names.
-/
lemma decisionName_isName {ι : Type*} [Small.{u} ι] (P : ZFSet.{u})
    (label condition : ι → ZFSet.{u}) (hc : ∀ i, condition i ∈ P) :
    IsName P (decisionName P label condition) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨check P (label i), condition i, rfl⟩
  · intro σ p hp
    obtain ⟨i, hi⟩ := ZFSet.mem_range.mp hp
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hi
    exact ⟨hc i, check_isName P (label i)⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Basic valuation calculations
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Its valuation formula follows by substituting $\check{a_i}^G=a_i$ into the defining recursion.
-/
lemma mem_valuation_decisionName {ι : Type*} [Small.{u} ι] (P : ZFSet.{u})
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) (label condition : ι → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ valuation G (decisionName P label condition) ↔ ∃ i, condition i ∈ G ∧ label i = x := by
  rw [mem_valuation]
  constructor
  · rintro ⟨σ, p, hp, hpair, hx⟩
    obtain ⟨i, hi⟩ := ZFSet.mem_range.mp hpair
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hi
    exact ⟨i, hp, (valuation_check P G hG (label i)).symm.trans hx⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨check P (label i), condition i, hi, ZFSet.mem_range_self i,
      valuation_check P G hG (label i)⟩

def genericName (P : ZFSet.{u}) : ZFSet.{u} := decisionName P (fun p : P => p.val) (fun p => p.val)

lemma genericName_isName (P : ZFSet.{u}) : IsName P (genericName P) :=
  decisionName_isName P _ _ (fun p => p.property)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The filter itself has the canonical name
    $$\dot G := \{\langle \check{p},p\rangle : p \in P\}.$$
    The lemma with labels $a_p=p$ gives $\dot G^G=G$.
-/
/-- The generic name evaluates to precisely the chosen conditions in P. -/
theorem valuation_genericName (P : ZFSet.{u}) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (genericName P) = P.sep (fun p => p ∈ G) := by
  apply ZFSet.ext
  intro x
  rw [genericName, mem_valuation_decisionName P G hG, ZFSet.mem_sep]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.property, hp⟩
  · rintro ⟨hp, hG⟩
    exact ⟨⟨x, hp⟩, hG, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For Cohen forcing $P=\finseq{2}$ ordered by extension, the canonical name for the generic real is
    $$\dot c := \{\Pair{\check{\Pair{n}{\varepsilon}}}{s} : s \in \finseq{2},\; n<\Length{s},\; s(n)=\varepsilon\}.$$
    Applying the same formula to the labels $\Pair{n}{\varepsilon}$ gives
    $$\dot c^G=\{\Pair{n}{\varepsilon}:\exists s\in G,\;n<\Length{s},\;s(n)=\varepsilon\}=\bigcup G.$$
-/
/-- If conditions are graphs, this is the name of their generic union. -/
def unionName (P : ZFSet.{u}) : ZFSet.{u} :=
  decisionName P (fun sz : (s : P) × s.val => sz.2.val) (fun sz => sz.1.val)

lemma unionName_isName (P : ZFSet.{u}) : IsName P (unionName P) :=
  decisionName_isName P _ _ (fun sz => sz.1.property)

theorem valuation_unionName (P : ZFSet.{u}) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) :
    valuation G (unionName P) = ZFSet.sUnion (P.sep (fun p => p ∈ G)) := by
  apply ZFSet.ext
  intro x
  rw [unionName, mem_valuation_decisionName P G hG, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨⟨s, z⟩, hs, rfl⟩
    exact ⟨s.val, ZFSet.mem_sep.mpr ⟨s.property, hs⟩, z.property⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨hsP, hsG⟩ := ZFSet.mem_sep.mp hs
    exact ⟨⟨⟨s, hsP⟩, ⟨x, hx⟩⟩, hsG, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The generic extension is
    $$M[G] := \{\tau^G : \tau \in M^P\}.$$
-/
/-- Evaluations of the names belonging to the given ground set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    These definitions make sense even before imposing genericity on $G$.
-/
def extension (P M : ZFSet.{u}) (G : Set ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun τ : {τ : M // IsName P τ.val} => valuation G τ.val.val)

lemma mem_extension (P M : ZFSet.{u}) (G : Set ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ extension P M G ↔ ∃ τ ∈ M, IsName P τ ∧ valuation G τ = x := by
  rw [extension, ZFSet.mem_range]
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨τ.val.val, τ.val.property, τ.property, hτ⟩
  · rintro ⟨τ, hτ, hn, hx⟩
    exact ⟨⟨⟨τ, hτ⟩, hn⟩, hx⟩

lemma child_mem_ground {M τ σ p : ZFSet.{u}} (hM : M.IsTransitive)
    (hτ : τ ∈ M) (hστ : pair σ p ∈ τ) : σ ∈ M := by
  have hpair : pair σ p ∈ M := hM.mem_trans hστ hτ
  have hs : ({σ} : ZFSet) ∈ M := hM.mem_trans (by simp [pair]) hpair
  exact hM.mem_trans (by simp) hs

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Take $x=\tau^G\in M[G]$ and $y\in x$. Some pair $\langle\sigma,p\rangle\in\tau$ with $p\in G$ satisfies
    $y=\sigma^G$. Since $\tau$ is a name, so is $\sigma$. Transitivity of $M$, applied successively along
    $$\sigma\in\{\sigma\}\in\langle\sigma,p\rangle\in\tau\in M,$$
    gives $\sigma\in M$. Thus $y\in M[G]$, proving transitivity.
    Under the additional check-name closure hypothesis, each $x\in M$ equals $\check{x}^G$ for a name in $M$,
    so $x\in M[G]$.
    \end{proof}
-/
/-- Transitivity of the extension does not require genericity. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Transitivity of the extension
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Forcing extensions $M[G]$ are transitive and contain $M$, so these tests explain which low-complexity assertions are
    preserved by forcing and which can change.
-/
theorem extension_isTransitive (P M : ZFSet.{u}) (G : Set ZFSet.{u})
    (hM : M.IsTransitive) : (extension P M G).IsTransitive := by
  intro x hx y hy
  obtain ⟨τ, hτM, hτ, rfl⟩ := (mem_extension P M G x).mp hx
  obtain ⟨σ, p, _, hστ, hσ⟩ := (mem_valuation G τ y).mp hy
  exact (mem_extension P M G y).mpr
    ⟨σ, child_mem_ground hM hτM hστ, hτ.child hστ, hσ⟩

/-- Ground inclusion uses check-name closure, which is a separate model-theoretic input. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Transitivity of the extension
-/
theorem ground_subset_extension (P M : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) (hcheck : ∀ x ∈ M, check P x ∈ M) : M ⊆ extension P M G := by
  intro x hx
  exact (mem_extension P M G x).mpr
    ⟨check P x, hcheck x hx, check_isName P x, valuation_check P G hG x⟩

end PolishSpaceBook.ForcingNames
