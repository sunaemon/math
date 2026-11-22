module

public import PolishSpaceBook.ForcingAtomic
public import PolishSpaceBook.SetTheoryInternalFixedPoint
public import PolishSpaceBook.SetTheoryInternalHierarchy

@[expose] public section

/-! # Positive table equations for the atomic forcing recursion -/

noncomputable section
namespace PolishSpaceBook.ForcingAtomic
open ZFSet ForcingNames SetTheoryModels
universe u

/-- The tag distinguishes membership and equality entries in a single set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{ForcingTableEntry}
    \end{mathmeta}
    For the atomic clauses, let $P,R,W,m,e\in M$, where $R$ codes the forcing order, $W$ is transitive,
    and $m\ne e$. The two tags distinguish membership from equality. Put
    $$\begin{aligned}
    \ForcingTableEntry{b}{p}{\sigma}{\tau}
    &:=\langle b,\langle p,\langle\sigma,\tau\rangle\rangle\rangle,\\
    B&:=\{m,e\}\times(P\times(W\times W)),\\
    T_b(p,\sigma,\tau)&\;:\Longleftrightarrow\;
     \ForcingTableEntry{b}{p}{\sigma}{\tau}\in T.
    \end{aligned}$$
    Pairing and the product construction give $B\in M$ under the closure axioms used above.
    Transitivity of $W$ makes it closed under child names: if $\tau\in W$ and
    $\langle\sigma,r\rangle\in\tau$, then $\sigma\in W$.
    The atomic clauses make sense on arbitrary sets, so we use them throughout $W$ and restrict to names at the end.
-/
def tableEntry (tag p σ τ : ZFSet.{u}) : ZFSet.{u} := pair tag (pair p (pair σ τ))

lemma tableEntry_inj (tag p σ τ tag' p' σ' τ' : ZFSet.{u}) :
    tableEntry tag p σ τ = tableEntry tag' p' σ' τ' ↔
      tag = tag' ∧ p = p' ∧ σ = σ' ∧ τ = τ' := by
  simp only [tableEntry, ZFSet.pair_inj]

def tableBound (P W m e : ZFSet.{u}) : ZFSet.{u} :=
  prod (insert m ({e} : ZFSet.{u})) (prod P (prod W W))

lemma tableEntry_mem_bound {P W m e tag p σ τ : ZFSet.{u}} :
    tableEntry tag p σ τ ∈ tableBound P W m e ↔
      (tag = m ∨ tag = e) ∧ p ∈ P ∧ σ ∈ W ∧ τ ∈ W := by
  simp only [tableBound, tableEntry, ZFSet.pair_mem_prod, ZFSet.mem_insert_iff, ZFSet.mem_singleton]

variable (P : ZFSet.{u}) [Preorder (Condition P)]

/-- The membership clause, with lookups in the candidate equality table. -/
def membershipTableStep (W e T σ τ : ZFSet.{u}) : Set (Condition P) :=
  forcingDense {q | ∃ π ∈ W, ∃ r : Condition P,
    pair π r.val ∈ τ ∧ q ≤ r ∧ tableEntry e q.val σ π ∈ T}

/-- One half of the equality clause, with lookups in the candidate membership table. -/
def equalityHalfTableStep (W m T σ τ : ZFSet.{u}) (p : Condition P) : Prop :=
  ∀ π ∈ W, ∀ r : Condition P, pair π r.val ∈ σ →
    p ∈ forcingDense {q | incompatible P q r ∨ tableEntry m q.val π τ ∈ T}

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    All condition variables below range over $P$. For a candidate table $T$, define
    $$\begin{aligned}
    A_T(p,\sigma,\tau)\;:\Longleftrightarrow\;
    &\forall q\le p\;\exists s\le q\;\exists\pi\in W\;\exists r\in P\\
    &\bigl(\langle\pi,r\rangle\in\tau\land s\le r\land T_e(s,\sigma,\pi)\bigr),\\
    E_T(p,\sigma,\tau)\;:\Longleftrightarrow\;
    &\forall\pi\in W\;\forall r\in P\;\bigl(\langle\pi,r\rangle\in\sigma\\
    &\longrightarrow\forall q\le p\;\exists s\le q\;
     (s\perp r\lor T_m(s,\pi,\tau))\bigr).
    \end{aligned}$$
    Define $\Phi(T)\IncludedIn B$ by the two clauses
    $$\begin{aligned}
    \ForcingTableEntry{m}{p}{\sigma}{\tau}\in\Phi(T)
    &\Longleftrightarrow A_T(p,\sigma,\tau),\\
    \ForcingTableEntry{e}{p}{\sigma}{\tau}\in\Phi(T)
    &\Longleftrightarrow E_T(p,\sigma,\tau)\land E_T(p,\tau,\sigma)
    \end{aligned}$$
    for $p\in P$ and $\sigma,\tau\in W$.

-/
def atomicTableStep (W m e T x : ZFSet.{u}) : Prop :=
  ∃ p : Condition P, ∃ σ ∈ W, ∃ τ ∈ W,
    (x = tableEntry m p.val σ τ ∧ p ∈ membershipTableStep P W e T σ τ) ∨
    (x = tableEntry e p.val σ τ ∧ equalityHalfTableStep P W m T σ τ p ∧
      equalityHalfTableStep P W m T τ σ p)

lemma membershipTableStep_mono {W e S T σ τ : ZFSet.{u}} (hST : S ⊆ T) :
    membershipTableStep P W e S σ τ ⊆ membershipTableStep P W e T σ τ := by
  intro p hp q hqp
  obtain ⟨s, hsq, π, hπ, r, hpair, hsr, hs⟩ := hp q hqp
  exact ⟨s, hsq, π, hπ, r, hpair, hsr, hST hs⟩

lemma equalityHalfTableStep_mono {W m S T σ τ : ZFSet.{u}} (hST : S ⊆ T) {p : Condition P}
    (hp : equalityHalfTableStep P W m S σ τ p) : equalityHalfTableStep P W m T σ τ p := by
  intro π hπ r hpair q hqp
  obtain ⟨s, hsq, hs⟩ := hp π hπ r hpair q hqp
  exact ⟨s, hsq, hs.imp_right (fun h => hST h)⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Every lookup in $T$ occurs positively, while incompatibility is independent of $T$.
    Thus enlarging $T$ preserves every witness and every universal requirement, proving monotonicity of $\Phi$.
-/
lemma atomicTableStep_mono {W m e S T : ZFSet.{u}} (hST : S ⊆ T) {x : ZFSet.{u}}
    (hx : atomicTableStep P W m e S x) : atomicTableStep P W m e T x := by
  obtain ⟨p, σ, hσ, τ, hτ, h⟩ := hx
  refine ⟨p, σ, hσ, τ, hτ, ?_⟩
  rcases h with ⟨he, hm⟩ | ⟨he, h1, h2⟩
  · exact Or.inl ⟨he, membershipTableStep_mono P hST hm⟩
  · exact Or.inr ⟨he, equalityHalfTableStep_mono P hST h1, equalityHalfTableStep_mono P hST h2⟩

omit [Preorder (Condition P)] in
lemma condition_val_injective : Function.Injective (Condition.val (P := P)) := by
  intro p q h
  cases p
  cases q
  cases h
  rfl

lemma step_membership_entry {W m e T σ τ : ZFSet.{u}} (hme : m ≠ e)
    (hσ : σ ∈ W) (hτ : τ ∈ W) (p : Condition P) :
    atomicTableStep P W m e T (tableEntry m p.val σ τ) ↔ p ∈ membershipTableStep P W e T σ τ := by
  constructor
  · rintro ⟨q, σ', _, τ', _, h⟩
    rcases h with ⟨he, hq⟩ | ⟨he, _, _⟩
    · obtain ⟨_, hpq, hσσ, hττ⟩ := (tableEntry_inj _ _ _ _ _ _ _ _).mp he
      have hpq' := condition_val_injective P hpq
      simpa only [hpq', hσσ, hττ] using hq
    · exact False.elim (hme ((tableEntry_inj _ _ _ _ _ _ _ _).mp he).1)
  · intro hp; exact ⟨p, σ, hσ, τ, hτ, Or.inl ⟨rfl, hp⟩⟩

lemma step_equality_entry {W m e T σ τ : ZFSet.{u}} (hme : m ≠ e)
    (hσ : σ ∈ W) (hτ : τ ∈ W) (p : Condition P) :
    atomicTableStep P W m e T (tableEntry e p.val σ τ) ↔
      equalityHalfTableStep P W m T σ τ p ∧ equalityHalfTableStep P W m T τ σ p := by
  constructor
  · rintro ⟨q, σ', _, τ', _, h⟩
    rcases h with ⟨he, _⟩ | ⟨he, h1, h2⟩
    · exact False.elim (hme ((tableEntry_inj _ _ _ _ _ _ _ _).mp he).1.symm)
    · obtain ⟨_, hpq, hσσ, hττ⟩ := (tableEntry_inj _ _ _ _ _ _ _ _).mp he
      have hpq' := condition_val_injective P hpq
      simpa only [hpq', hσσ, hττ] using And.intro h1 h2
  · rintro ⟨h1, h2⟩; exact ⟨p, σ, hσ, τ, hτ, Or.inr ⟨rfl, h1, h2⟩⟩

/-- A fixed table satisfies the two displayed equations at each valid pair of inputs. -/
lemma fixed_table_equations {W m e T : ZFSet.{u}} (hme : m ≠ e)
    (hfix : (tableBound P W m e).sep (atomicTableStep P W m e T) = T)
    {σ τ : ZFSet.{u}} (hσ : σ ∈ W) (hτ : τ ∈ W) (p : Condition P) :
    (tableEntry m p.val σ τ ∈ T ↔ p ∈ membershipTableStep P W e T σ τ) ∧
    (tableEntry e p.val σ τ ∈ T ↔
      equalityHalfTableStep P W m T σ τ p ∧ equalityHalfTableStep P W m T τ σ p) := by
  have hm : tableEntry m p.val σ τ ∈ tableBound P W m e :=
    tableEntry_mem_bound.mpr ⟨Or.inl rfl, p.property, hσ, hτ⟩
  have he : tableEntry e p.val σ τ ∈ tableBound P W m e :=
    tableEntry_mem_bound.mpr ⟨Or.inr rfl, p.property, hσ, hτ⟩
  constructor
  · conv_lhs => rw [← hfix, ZFSet.mem_sep]
    rw [and_iff_right hm, step_membership_entry P hme hσ hτ p]
  · conv_lhs => rw [← hfix, ZFSet.mem_sep]
    rw [and_iff_right he, step_equality_entry P hme hσ hτ p]

/-- Every fixed table on a child-closed domain agrees with the external atomic recursion. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Agreement with the atomic recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Induct on the sorted rank-pair from §{sec:forcing-relation}, proving both equivalences together.
    At a membership entry the fixed-point equation is $A_C(p,\sigma,\tau)$.
    Every contributing child $\pi$ belongs to $W$, and its equality lookup has a strictly smaller rank-pair.
    The induction hypothesis converts that lookup into $s\forces^*\sigma=\pi$, yielding exactly the atomic
    membership clause in both directions. At an equality entry, apply the same argument to the two halves
    $E_C(p,\sigma,\tau)$ and $E_C(p,\tau,\sigma)$; their membership lookups also have smaller rank-pairs.
    Transitivity of $W$ ensures that restricting the child quantifiers to $W$ discards no witness.
    The resulting equations are precisely the two equality clauses.
-/
theorem fixed_table_iff_atomic {W m e T : ZFSet.{u}} (hme : m ≠ e)
    (hfix : (tableBound P W m e).sep (atomicTableStep P W m e T) = T)
    (hW : ∀ τ ∈ W, ∀ σ (p : Condition P), pair σ p.val ∈ τ → σ ∈ W)
    (b : Bool) (σ τ : ZFSet.{u}) (hσ : σ ∈ W) (hτ : τ ∈ W) (p : Condition P) :
    tableEntry (if b then e else m) p.val σ τ ∈ T ↔ p ∈ atomic P b σ τ := by
  cases b
  · change tableEntry m p.val σ τ ∈ T ↔ p ∈ atomic P false σ τ
    rw [(fixed_table_equations P hme hfix hσ hτ p).1, membership_eq]
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    apply exists_congr
    intro s
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨π, hπ, r, hπτ, hsr, he⟩
      exact ⟨π, r, hπτ, hsr, (fixed_table_iff_atomic hme hfix hW true σ π hσ hπ s).mp he⟩
    · rintro ⟨π, r, hπτ, hsr, he⟩
      have hπ := hW τ hτ π r hπτ
      exact ⟨π, hπ, r, hπτ, hsr, (fixed_table_iff_atomic hme hfix hW true σ π hσ hπ s).mpr he⟩
  · change tableEntry e p.val σ τ ∈ T ↔ p ∈ atomic P true σ τ
    rw [(fixed_table_equations P hme hfix hσ hτ p).2, equality_iff]
    have half (a c : ZFSet.{u}) (ha : a ∈ W)
        (ih : ∀ π (r : Condition P), pair π r.val ∈ a → ∀ q : Condition P,
          tableEntry m q.val π c ∈ T ↔ q ∈ atomic P false π c) :
        equalityHalfTableStep P W m T a c p ↔
          ∀ π (r : Condition P), pair π r.val ∈ a → p ∈ forcingDense
            {q | incompatible P q r ∨ q ∈ atomic P false π c} := by
      constructor
      · intro h π r hπ q hqp
        obtain ⟨s, hsq, hs⟩ := h π (hW a ha π r hπ) r hπ q hqp
        exact ⟨s, hsq, hs.imp_right (fun ht => (ih π r hπ s).mp ht)⟩
      · intro h π _ r hπ q hqp
        obtain ⟨s, hsq, hs⟩ := h π r hπ q hqp
        exact ⟨s, hsq, hs.imp_right (fun ht => (ih π r hπ s).mpr ht)⟩
    exact and_congr
      (half σ τ hσ (fun π r hπ q =>
        fixed_table_iff_atomic hme hfix hW false π τ (hW σ hσ π r hπ) hτ q))
      (half τ σ hτ (fun π r hπ q =>
        fixed_table_iff_atomic hme hfix hW false π σ (hW τ hτ π r hπ) hσ q))
termination_by (max σ.rank τ.rank, min σ.rank τ.rank)
decreasing_by
  · exact sorted_lt_right (child_rank_lt hπτ)
  · exact sorted_lt_right (child_rank_lt hπτ)
  · exact sorted_lt_left (child_rank_lt hπ)
  · have h := sorted_lt_right (a := σ.rank) (child_rank_lt hπ)
    rw [max_comm σ.rank π.rank, min_comm σ.rank π.rank] at h
    exact h

/-- Equality at the encoded entries implies uniqueness of a fixed table on the whole bound. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Agreement with the atomic recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Since all elements of $B$ are uniquely tagged
    records, agreement at all entries gives uniqueness of the whole table.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The rank-pair argument in §{sec:forcing-relation} constructs the atomic relations externally.
    We now give their internal definitions, using the internal least-fixed-point construction in
    §{sec:internal-model-fixed-points}. We show that the atomic recursion is the unique possible fixed table on each
    suitable bound.
-/
theorem fixed_table_unique {W m e S T : ZFSet.{u}} (hme : m ≠ e)
    (hS : (tableBound P W m e).sep (atomicTableStep P W m e S) = S)
    (hT : (tableBound P W m e).sep (atomicTableStep P W m e T) = T)
    (hW : ∀ τ ∈ W, ∀ σ (p : Condition P), pair σ p.val ∈ τ → σ ∈ W) : S = T := by
  have incl (A B : ZFSet.{u})
      (hA : (tableBound P W m e).sep (atomicTableStep P W m e A) = A)
      (hB : (tableBound P W m e).sep (atomicTableStep P W m e B) = B) : A ⊆ B := by
    intro x hx
    have hbound : x ∈ tableBound P W m e := by rw [← hA] at hx; exact (ZFSet.mem_sep.mp hx).1
    obtain ⟨tag, htag, q, hq, rfl⟩ := ZFSet.mem_prod.mp hbound
    obtain ⟨p, hp, r, hr, rfl⟩ := ZFSet.mem_prod.mp hq
    obtain ⟨σ, hσ, τ, hτ, rfl⟩ := ZFSet.mem_prod.mp hr
    have htag' : tag = m ∨ tag = e := by simpa using htag
    rcases htag' with rfl | rfl
    · exact (fixed_table_iff_atomic P hme hB hW false σ τ hσ hτ ⟨p, hp⟩).mpr
        ((fixed_table_iff_atomic P hme hA hW false σ τ hσ hτ ⟨p, hp⟩).mp hx)
    · exact (fixed_table_iff_atomic P hme hB hW true σ τ hσ hτ ⟨p, hp⟩).mpr
        ((fixed_table_iff_atomic P hme hA hW true σ τ hσ hτ ⟨p, hp⟩).mp hx)
  exact ZFSet.ext (fun _ => ⟨fun h => incl S T hS hT h, fun h => incl T S hT hS h⟩)

end PolishSpaceBook.ForcingAtomic
