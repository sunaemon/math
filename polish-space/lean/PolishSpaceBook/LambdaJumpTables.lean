module

public import PolishSpaceBook.LambdaNotationBounds
public import PolishSpaceBook.LambdaIteratedJump
public import PolishSpaceBook.LambdaBaireQuantifiers

@[expose] public section

/-! # Witness tables for iterated jumps

A witness supplies a downward-closed domain and a bit-valued table on all
numerical rows. Its local conditions use finite candidate certificates,
never a decision procedure for notation validity. Validity is used only
in proving existence and uniqueness of the rows that matter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative
set_option maxHeartbeats 800000

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
    Decode a sequence $q$ into
    $$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
    The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
    certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
    certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
    Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
    and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
    Both tests terminate for every input; no indexed computation is run to completion.
-/
def tableDomain (q : ℕ → ℕ) (a : ℕ) : Prop := leftBaire q a = 1

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
    Decode a sequence $q$ into
    $$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
    The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
    certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
    certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
    Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
    and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
    Both tests terminate for every input; no indexed computation is run to completion.
-/
def tableRow (q : ℕ → ℕ) (a n : ℕ) : ℕ := rightBaire q (Nat.pair a n)

/-- Local equations on an arbitrary downward-closed collection of row indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    A single sequence $q\in\BaireSpace$ can record a domain $D$ and numerical rows $G_b$ by
    $$D:=\{b:\LambdaNumericProjection{1}(q(b))=1\},\qquad
     G_b(n):=\LambdaNumericProjection{2}(q(\NatPair{b}{n})).$$
    Here numerical projections mean the numerical functions computed by the corresponding closed terms.
    Use the decidable certificate predicate $C$ from §{sec:lambda-certified-descent}.
    Call $q$ a \termdefine{jump witness table} over $A\IncludedIn\NN$ when the following conditions hold.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    1. Every value $G_b(n)$ is zero or one.
    2. If $p\in D$ and $C(p,\NatPair{b}{c})$, then $b\in D$.
    3. If $1\in D$, then $G_1=\chi_A$.
    4. If $b>0$ and $2^b\in D$, then $G_{2^b}(n)=1$ exactly when the closed program $P_n$,
       with input function $G_b$ and numerical argument $n$, returns a numeral in finitely many beta/query steps.
    5. If $3\cdot5^e\in D$ and a finite certificate verifies $\varphi_e(i)=b$, then
       $G_{3\cdot5^e}(\NatPair{i}{m})=G_b(m)$ for every $m$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
    Decode a sequence $q$ into
    $$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
    The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
    certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
    certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
    Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
    and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
    Both tests terminate for every input; no indexed computation is run to completion.
-/
structure JumpTable (A : Set ℕ) (q : ℕ → ℕ) : Prop where
  bits : ∀ a n, tableRow q a n = 0 ∨ tableRow q a n = 1
  down : ∀ p b c, tableDomain q p → edgeCertificate (Nat.pair p (Nat.pair b c)) → tableDomain q b
  zero : tableDomain q 1 → ∀ n, tableRow q 1 n = characteristic A n
  succ : ∀ b, 0 < b → tableDomain q (successorCode b) → ∀ n,
    (tableRow q (successorCode b) n = 1 ↔ n ∈ Jump (tableRow q b))
  limit : ∀ e i b s, tableDomain q (limitCode e) → Term.outputTest e i b s = true → ∀ m,
    tableRow q (limitCode e) (Nat.pair i m) = tableRow q b m

theorem JumpTable.edge_down {A : Set ℕ} {q : ℕ → ℕ} (h : JumpTable A q)
    {p b : ℕ} (hp : tableDomain q p) (hb : Edge b p) : tableDomain q b := by
  obtain ⟨c,hc⟩ := edgeCertificate_complete p b hb
  exact h.down p b c hp hc

theorem valid_limit_data {e : ℕ} (he : Valid (limitCode e)) :
    ∃ f : ℕ → ℕ, NumericalComputes (Term.closedProgram e) f ∧
      (∀ n, Valid (f n)) ∧ (∀ n, RawPrecedes (f n) (f (n+1))) := by
  generalize hx : limitCode e = a at he
  cases he with
  | zero => have h := limitCode_ge_three e; omega
  | @succ a ha => exact (successorCode_ne_limitCode a e hx.symm).elim
  | limit d f hc hf hi =>
    have hed := limitCode_injective hx
    subst d
    exact ⟨f,hc,hf,hi⟩

noncomputable def canonicalTableEntry (A : Set ℕ) (z : ℕ × ℕ) : ℕ := by
  classical
  exact if h : Valid z.1 then characteristic (iteratedJump A z.1 h) z.2 else 0

noncomputable def canonicalJumpTable (A : Set ℕ) : ℕ → ℕ :=
  pairBaire (characteristic {a | Valid a}) (fun z => canonicalTableEntry A z.unpair)

@[simp] theorem canonicalJumpTable_domain (A : Set ℕ) (a : ℕ) :
    tableDomain (canonicalJumpTable A) a ↔ Valid a := by
  classical
  simp [tableDomain,canonicalJumpTable,characteristic]

theorem canonicalJumpTable_row (A : Set ℕ) (a : ℕ) (ha : Valid a) (n : ℕ) :
    tableRow (canonicalJumpTable A) a n = characteristic (iteratedJump A a ha) n := by
  classical
  unfold tableRow canonicalJumpTable
  rw [rightBaire_pair]
  rw [Nat.unpair_pair]
  simp only [canonicalTableEntry, dite_eq_left ha]

theorem characteristic_join_pair (F : ℕ → Set ℕ) (i m : ℕ) :
    characteristic (effectiveJoin F) (Nat.pair i m) = characteristic (F i) m := by
  classical
  simp only [characteristic, effectiveJoin, Set.mem_ofPred_eq, Nat.unpair_pair]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For existence, take $D=\KleeneO$, put $G_b=\chi_{\IteratedJump{A}{b}}$ on valid rows, and put zero
    on all other rows. Validity is downward closed under candidate steps. The iteration equations therefore
    verify all five conditions, including every certified output at a limit. Pair the domain bits and the row
    values into $q$. This is an existence construction; it does not provide a procedure for deciding validity.
-/
theorem canonicalJumpTable_spec (A : Set ℕ) : JumpTable A (canonicalJumpTable A) := by
  classical
  constructor
  · intro a n
    unfold tableRow canonicalJumpTable
    rw [rightBaire_pair]
    rw [Nat.unpair_pair]
    simp only [canonicalTableEntry]
    split_ifs
    · unfold characteristic
      split_ifs <;> simp
    · simp
  · intro p b c hp hc
    rw [canonicalJumpTable_domain] at hp ⊢
    exact hp.edge_down (by simpa only [Nat.unpair_pair] using edgeCertificate_sound p (Nat.pair b c) hc)
  · intro _ n
    rw [canonicalJumpTable_row A 1 .zero,iteratedJump_zero]
  · intro b hb hp n
    have hv := (canonicalJumpTable_domain A _).mp hp
    have hvb := hv.edge_down (.succ b hb)
    rw [canonicalJumpTable_row A _ hv]
    have he : iteratedJump A (successorCode b) hv = Jump (characteristic (iteratedJump A b hvb)) :=
      (iteratedJump_spec A _ hv).unique (.succ (iteratedJump_spec A b hvb))
    have hr : tableRow (canonicalJumpTable A) b = characteristic (iteratedJump A b hvb) :=
      funext (canonicalJumpTable_row A b hvb)
    rw [he,hr]
    simp [characteristic]
  · intro e i b s hp ht m
    have hv := (canonicalJumpTable_domain A _).mp hp
    obtain ⟨f,hf,hvF,hi⟩ := valid_limit_data hv
    have hb : b = f i := runs_unique ((outputTest_exists_iff e i b).mp ⟨s,ht⟩) (hf.2 i)
    subst b
    rw [canonicalJumpTable_row A _ hv,canonicalJumpTable_row A _ (hvF i)]
    rw [iteratedJump_limit A e f hf hvF hi]
    exact characteristic_join_pair _ i m

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For uniqueness, induct on the generation of $a\in\KleeneO$. The row for the zero notation is prescribed. At a
    successor, a certificate for the preceding step places the preceding notation in $D$; the induction
    hypothesis identifies its row, and the jump condition determines the new row. At a limit, each value
    $\varphi_e(i)$ has a finite output certificate. Downward closure places that notation in $D$, and the
    induction hypothesis identifies its row. The fifth condition then determines every entry of the joined
    row. Thus all rows needed below a valid $a$ are forced, even if $D$ also contains invalid indices.
    \end{proof}
-/
theorem JumpTable.row_unique {A : Set ℕ} {q : ℕ → ℕ} (h : JumpTable A q)
    (a : ℕ) (ha : Valid a) (hd : tableDomain q a) :
    tableRow q a = characteristic (iteratedJump A a ha) := by
  classical
  induction ha with
  | zero => simpa only [iteratedJump_zero] using funext (h.zero hd)
  | @succ a ha ih =>
    have hd' := h.edge_down hd (.succ a ha.pos)
    have hr := ih hd'
    rw [iteratedJump_successor A a ha]
    funext n
    have hs := h.succ a ha.pos hd n
    rw [hr] at hs
    rcases h.bits (successorCode a) n with hz | ho
    · have hn : n ∉ Jump (characteristic (iteratedJump A a ha)) := by
        intro hn
        have := hs.mpr hn
        omega
      simp [hz,characteristic,hn]
    · simp [ho,characteristic,hs.mp ho]
  | limit e f hc hf hi ih =>
    rw [iteratedJump_limit A e f hc hf hi]
    funext z
    obtain ⟨s,hs⟩ := (outputTest_exists_iff e z.unpair.1 (f z.unpair.1)).mpr (hc.2 z.unpair.1)
    have hd' := h.edge_down hd (.limit e z.unpair.1 _ (hc.2 z.unpair.1))
    have he := h.limit e z.unpair.1 (f z.unpair.1) s hd hs z.unpair.2
    rw [Nat.pair_unpair,ih z.unpair.1 hd'] at he
    have hchar : characteristic (effectiveJoin (fun i => iteratedJump A (f i) (hf i))) z =
        characteristic (iteratedJump A (f z.unpair.1) (hf z.unpair.1)) z.unpair.2 := rfl
    exact he.trans hchar.symm

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: lemma
  title: Existence and uniqueness of the required rows
-/
theorem jumpTable_existence_unique (A : Set ℕ) :
    (∃ q, JumpTable A q ∧ ∀ a, Valid a → tableDomain q a) ∧
    (∀ q, JumpTable A q → ∀ a (ha : Valid a), tableDomain q a →
      tableRow q a = characteristic (iteratedJump A a ha)) := by
  exact ⟨⟨canonicalJumpTable A,canonicalJumpTable_spec A,
    fun a ha => (canonicalJumpTable_domain A a).mpr ha⟩,
    fun _ h a ha hd => h.row_unique a ha hd⟩

theorem iteratedJump_membership_table (A : Set ℕ) (a : ℕ) (ha : Valid a) (n : ℕ) :
    n ∈ iteratedJump A a ha ↔ ∃ q, JumpTable A q ∧ tableDomain q a ∧ tableRow q a n = 1 := by
  classical
  constructor
  · intro hn
    exact ⟨canonicalJumpTable A,canonicalJumpTable_spec A,
      (canonicalJumpTable_domain A a).mpr ha,by rw [canonicalJumpTable_row A a ha]; simp [characteristic,hn]⟩
  · rintro ⟨q,hq,hd,hn⟩
    rw [hq.row_unique a ha hd] at hn
    simpa [characteristic] using hn

theorem iteratedJump_nonmembership_table (A : Set ℕ) (a : ℕ) (ha : Valid a) (n : ℕ) :
    n ∉ iteratedJump A a ha ↔ ∃ q, JumpTable A q ∧ tableDomain q a ∧ tableRow q a n = 0 := by
  classical
  constructor
  · intro hn
    exact ⟨canonicalJumpTable A,canonicalJumpTable_spec A,
      (canonicalJumpTable_domain A a).mpr ha,by rw [canonicalJumpTable_row A a ha]; simp [characteristic,hn]⟩
  · rintro ⟨q,hq,hd,hn⟩
    rw [hq.row_unique a ha hd] at hn
    simpa [characteristic] using hn

end KleeneNotation
end PolishSpaceBook
