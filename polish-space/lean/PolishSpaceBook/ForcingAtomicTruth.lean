module

public import PolishSpaceBook.ForcingAtomic
public import PolishSpaceBook.RandomGenericReals

@[expose] public section

/-!
# Truth for atomic forcing

The filter must meet the explicit membership and equality tests for names in
its transitive ground set. No ground-model definability is hidden in this
hypothesis. `ForcingInternalTests` supplies the ground-model codes and
`ForcingGenericTruth` applies them to every model-generic filter.
-/

noncomputable section
namespace PolishSpaceBook.ForcingAtomic
open ZFSet ForcingNames
universe u
variable (P : ZFSet.{u}) [Preorder (Condition P)]

def chosen (G : Order.PFilter (Condition P)) : Set ZFSet.{u} :=
  {p | ∃ r ∈ G, r.val = p}

def value (G : Order.PFilter (Condition P)) (τ : ZFSet.{u}) : ZFSet.{u} :=
  valuation (chosen P G) τ

lemma mem_value (G : Order.PFilter (Condition P)) (τ x : ZFSet.{u}) :
    x ∈ value P G τ ↔ ∃ (σ : ZFSet.{u}) (r : Condition P),
      r ∈ G ∧ pair σ r.val ∈ τ ∧ value P G σ = x := by
  rw [value, mem_valuation]
  constructor
  · rintro ⟨σ, p, ⟨r, hrG, rfl⟩, hστ, hx⟩
    exact ⟨σ, r, hrG, hστ, hx⟩
  · rintro ⟨σ, r, hrG, hστ, hx⟩
    exact ⟨σ, r.val, ⟨r, hrG, rfl⟩, hστ, hx⟩

structure MeetsAtomicTests (M : ZFSet.{u}) (G : Order.PFilter (Condition P)) : Prop where
  membership : ∀ σ ∈ M, IsName P σ → ∀ τ ∈ M, IsName P τ →
    ∃ p ∈ G, p ∈ forcingDecision (membershipWitness P σ τ)
  equality : ∀ σ ∈ M, IsName P σ → ∀ τ ∈ M, IsName P τ → ∃ p ∈ G, p ∈ equalityTest P σ τ

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \emph{Atomic, $\sigma \in \tau$, direction (‡).} If $p \in G$ has $p \forces^* \sigma \in \tau$, the dense set in the
    clause meets $G$ at some $q \in G$, witnessed by $\langle \pi,r\rangle \in \tau$ with $q \le r$ and $q \forces^* \sigma
    = \pi$. By the rank-pair induction (‡) applied to $\sigma = \pi$, $\sigma^G = \pi^G$. Since $r \in G$ and $\langle
    \pi,r\rangle \in \tau$, the valuation gives $\pi^G \in \tau^G$, hence $\sigma^G \in \tau^G$. Conversely, if $\sigma^G
    \in \tau^G$, the valuation of $\tau$ produces $\langle \pi, r\rangle \in \tau$ with $r \in G$ and $\pi^G = \sigma^G$.
    Rank-pair induction (‡) applied to $\sigma = \pi$ gives some $q' \in G$ with $q' \forces^* \sigma = \pi$. Take $q \in G$
    with $q \le q', r$ (using directedness of $G$). Then $q$ belongs to the witness set in the $\sigma \in \tau$ clause, and
    every stronger condition below $q$ also belongs to that set by monotonicity. Hence the witness set is dense below $q$,
    so $q \forces^* \sigma \in \tau$. Since $q \in G$, this supplies the forcing condition required by (‡).
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \emph{Atomic, $\sigma = \tau$.} Suppose $p\in G$ and $p\forces^*\sigma=\tau$.
    Take $\langle\pi,r\rangle\in\sigma$ with $r\in G$, and choose $q\in G$ with $q\le p,r$.
    We first show $q\forces^*\pi\in\tau$. Given $s\le q$, the equality clause supplies $t\le s$ that is incompatible
    with $r$ or forces $\pi\in\tau$. Since $t\le r$, incompatibility is impossible.
    Thus the conditions forcing $\pi\in\tau$ are dense below $q$, and density-saturation gives
    $q\forces^*\pi\in\tau$. Rank-pair induction now gives $\pi^G\in\tau^G$.
    Every element of $\sigma^G$ has this form, so $\sigma^G\IncludedIn\tau^G$.
    Swapping the two names gives the reverse inclusion.

    Conversely, suppose $\sigma^G=\tau^G$ and let $G$ meet $D(\sigma,\tau)$.
    A condition $q\in G\cap F(\sigma,\tau)$ would give a pair $\langle\pi,r\rangle\in\sigma$ with $q\le r$.
    Upward closure puts $r$ in $G$, so $\pi^G\in\sigma^G=\tau^G$.
    By the lower-rank truth lemma, some condition in $G$ forces $\pi\in\tau$.
    A common strengthening with $q$ contradicts the definition of $F(\sigma,\tau)$.
    The symmetric defect set is excluded in the same way. Hence $G$ contains a condition forcing $\sigma=\tau$.
    This proves (‡) for equality, and the preceding general argument gives (†).
-/
/-- The simultaneous rank induction proves both directions of atomic truth. -/
theorem atomic_truth (M : ZFSet.{u}) (hM : M.IsTransitive)
    (G : Order.PFilter (Condition P)) (hG : MeetsAtomicTests P M G)
    (b : Bool) (σ τ : ZFSet.{u}) (hσ : σ ∈ M) (hτ : τ ∈ M) (hσn : IsName P σ) (hτn : IsName P τ) :
    (∃ p ∈ G, p ∈ atomic P b σ τ) ↔
      if b then value P G σ = value P G τ else value P G σ ∈ value P G τ := by
  cases b
  · change (∃ p ∈ G, p ∈ atomic P false σ τ) ↔ value P G σ ∈ value P G τ
    constructor
    · rintro ⟨p, hpG, hp⟩
      rw [membership_eq] at hp
      obtain ⟨q, hqG, π, r, hπ, hqr, hq⟩ :=
        pfilter_dense_witness G hpG hp (hG.membership σ hσ hσn τ hτ hτn)
      have he := (atomic_truth M hM G hG true σ π hσ (child_mem_ground hM hτ hπ) hσn (hτn.child hπ)).mp ⟨q, hqG, hq⟩
      exact (mem_value P G τ _).mpr ⟨π, r, G.mem_of_le hqr hqG, hπ, he.symm⟩
    · intro h
      obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G τ _).mp h
      obtain ⟨q, hqG, hq⟩ :=
        (atomic_truth M hM G hG true σ π hσ (child_mem_ground hM hτ hπ) hσn (hτn.child hπ)).mpr he.symm
      obtain ⟨p, hpG, hpq, hpr⟩ := G.directed q hqG r hrG
      exact ⟨p, hpG, membership_of_witness P
        ⟨π, r, hπ, hpr, atomic_lower P true σ π hpq hq⟩⟩
  · change (∃ p ∈ G, p ∈ atomic P true σ τ) ↔ value P G σ = value P G τ
    constructor
    · rintro ⟨p, hpG, hp⟩
      apply ZFSet.ext
      intro x
      constructor
      · intro hx
        obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G σ x).mp hx
        obtain ⟨q, hqG, hqp, hqr⟩ := G.directed p hpG r hrG
        have hq := equality_member P (atomic_lower P true σ τ hqp hp) hπ hqr
        have hv := (atomic_truth M hM G hG false π τ (child_mem_ground hM hσ hπ) hτ (hσn.child hπ) hτn).mp ⟨q, hqG, hq⟩
        exact he ▸ hv
      · intro hx
        obtain ⟨π, r, hrG, hπ, he⟩ := (mem_value P G τ x).mp hx
        obtain ⟨q, hqG, hqp, hqr⟩ := G.directed p hpG r hrG
        have hq := equality_member P (equality_symm P σ τ (atomic_lower P true σ τ hqp hp)) hπ hqr
        have hv := (atomic_truth M hM G hG false π σ (child_mem_ground hM hτ hπ) hσ (hτn.child hπ) hσn).mp ⟨q, hqG, hq⟩
        exact he ▸ hv
    · intro he
      obtain ⟨p, hpG, (hp | hp) | hp⟩ := hG.equality σ hσ hσn τ hτ hτn
      · exact ⟨p, hpG, hp⟩
      · obtain ⟨π, r, hπ, hpr, hp⟩ := hp
        have hv : value P G π ∈ value P G σ :=
          (mem_value P G σ _).mpr ⟨π, r, G.mem_of_le hpr hpG, hπ, rfl⟩
        rw [he] at hv
        obtain ⟨q, hqG, hq⟩ :=
          (atomic_truth M hM G hG false π τ (child_mem_ground hM hσ hπ) hτ (hσn.child hπ) hτn).mpr hv
        exact False.elim (pfilter_not_pos_neg G (atomic_lower P false π τ) hqG hpG hq hp)
      · obtain ⟨π, r, hπ, hpr, hp⟩ := hp
        have hv : value P G π ∈ value P G τ :=
          (mem_value P G τ _).mpr ⟨π, r, G.mem_of_le hpr hpG, hπ, rfl⟩
        rw [← he] at hv
        obtain ⟨q, hqG, hq⟩ :=
          (atomic_truth M hM G hG false π σ (child_mem_ground hM hτ hπ) hσ (hτn.child hπ) hσn).mpr hv
        exact False.elim (pfilter_not_pos_neg G (atomic_lower P false π σ) hqG hpG hq hp)
termination_by (max σ.rank τ.rank, min σ.rank τ.rank)
decreasing_by
  all_goals first
    | exact sorted_lt_right (child_rank_lt hπ)
    | exact sorted_lt_left (child_rank_lt hπ)
    | have h := sorted_lt_right (a := σ.rank) (child_rank_lt hπ)
      rw [max_comm σ.rank π.rank, min_comm σ.rank π.rank] at h
      exact h

def groundNames (M : ZFSet.{u}) : Set ZFSet.{u} := {σ | σ ∈ M ∧ IsName P σ}

/-- Exactly the two explicit tests for every pair of ground-set names. -/
def atomicTests (M : ZFSet.{u}) : Set (Set (Condition P)) :=
  (fun st : ZFSet.{u} × ZFSet.{u} => forcingDecision (membershipWitness P st.1 st.2)) ''
    (groundNames P M ×ˢ groundNames P M) ∪
  (fun st : ZFSet.{u} × ZFSet.{u} => equalityTest P st.1 st.2) '' (groundNames P M ×ˢ groundNames P M)

lemma atomicTests_countable (M : ZFSet.{u}) (hc : M.toSet.Countable) : (atomicTests P M).Countable :=
by
  have hn : (groundNames P M).Countable := hc.mono (fun _ h => h.1)
  exact ((hn.prod hn).image _).union ((hn.prod hn).image _)

lemma atomicTests_dense (M : ZFSet.{u}) : ∀ D ∈ atomicTests P M, IsCoinitial D := by
  intro D hD
  rcases hD with ⟨⟨σ, τ⟩, _, rfl⟩ | ⟨⟨σ, τ⟩, _, rfl⟩
  · exact forcingDecision_dense _
  · exact equalityTest_dense P σ τ

/-- The countable descending-chain construction supplies a test filter through any condition. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For atomic formulas, this induction only needs the two displayed tests for each pair of names in $M$.
    It uses transitivity of $M$ to keep each child name in $M$, as proved in §{sec:forcing-names-valuation}.
    If $M$ is countable, these tests form a countable family of dense sets. The descending-chain construction therefore
    produces a filter meeting all of them through any prescribed condition.
-/
theorem exists_atomic_test_filter (M : ZFSet.{u}) (hc : M.toSet.Countable) (p : Condition P) :
    ∃ G : Order.PFilter (Condition P), p ∈ G ∧ MeetsAtomicTests P M G := by
  obtain ⟨G, hpG, hG⟩ := pfilter_meets_countable_dense (atomicTests P M)
    (atomicTests_countable P M hc) (atomicTests_dense P M) p
  refine ⟨G, hpG, ?_, ?_⟩
  · intro σ hσ hσn τ hτ hτn
    exact hG _ (Or.inl ⟨(σ, τ), ⟨⟨hσ, hσn⟩, ⟨hτ, hτn⟩⟩, rfl⟩)
  · intro σ hσ hσn τ hτ hτn
    exact hG _ (Or.inr ⟨(σ, τ), ⟨⟨hσ, hσn⟩, ⟨hτ, hτn⟩⟩, rfl⟩)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $\mathcal G$ be the family of such filters. For either atomic formula $\varphi$, the argument also proves
    $$p\forces^*\varphi
    \quad\Longleftrightarrow\quad
    \forall G\in\mathcal G,\;p\in G\Longrightarrow M[G]\models\varphi.$$
    For the converse, if the condition does not force the formula, density-saturation supplies
    $q\le p$ below which no condition forces $\varphi$.
    Choose a test filter through $q$ and apply atomic truth; directedness then contradicts any forcing condition in that
    filter. To pass from these explicit tests to the original model-theoretic statement, use their membership in $M$
    and the existence of $M$-generic filters through every condition.
-/
/-- Forcing has its semantic meaning already on the explicit atomic test filters.
The bridge to all M-generic filters is proved in `ForcingGenericTruth`. -/
theorem atomic_iff_all_test_filters (M : ZFSet.{u}) (hM : M.IsTransitive) (hc : M.toSet.Countable)
    (b : Bool) (σ τ : ZFSet.{u}) (hσ : σ ∈ M) (hτ : τ ∈ M) (hσn : IsName P σ) (hτn : IsName P τ) (p : Condition P) :
    p ∈ atomic P b σ τ ↔ ∀ G : Order.PFilter (Condition P), MeetsAtomicTests P M G → p ∈ G →
      if b then value P G σ = value P G τ else value P G σ ∈ value P G τ := by
  classical
  constructor
  · intro hp G hG hpG
    exact (atomic_truth P M hM G hG b σ τ hσ hτ hσn hτn).mp ⟨p, hpG, hp⟩
  · intro hs
    by_contra hp
    have hd : p ∉ forcingDense (atomic P b σ τ) := fun h => hp (atomic_saturated P b σ τ h)
    simp only [forcingDense, Set.mem_ofPred_eq] at hd
    push Not at hd
    obtain ⟨q, hqp, hq⟩ := hd
    obtain ⟨G, hqG, hG⟩ := exists_atomic_test_filter P M hc q
    have hv := hs G hG (G.mem_of_le hqp hqG)
    obtain ⟨r, hrG, hr⟩ := (atomic_truth P M hM G hG b σ τ hσ hτ hσn hτn).mpr hv
    exact pfilter_not_pos_neg G (atomic_lower P b σ τ) hrG hqG hr hq

end PolishSpaceBook.ForcingAtomic
