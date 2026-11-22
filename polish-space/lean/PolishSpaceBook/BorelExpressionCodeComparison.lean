module

public import PolishSpaceBook.BorelExpressionFold
public import PolishSpaceBook.BorelExpressionConstructors
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

/-! # External and inductive Borel codes: semantics and ordinal measures -/

namespace PolishSpaceBook
open Set
open scoped Ordinal

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The \termdefineas{tree rank}{structural rank} of a code measures the nesting of its constructors. Define it by
    structural recursion:
    $$
    \begin{aligned}
    \rho(\BorelLeafCode{n})&=0,\\
    \rho(\BorelComplementCode{d})&=\rho(d)+1,\\
    \rho(\BorelUnionCode{\Sequence{d_k}{k\in\omega}})&=\sup_k(\rho(d_k)+1).
    \end{aligned}
    $$
    Every immediate subcode has smaller rank. Thus recursion on subcodes is justified even when there is no
    common finite bound on their nesting depths.
-/
/-- The structural rank is defined by recursion on the Borel-code constructors. -/
noncomputable def BorelCode.nodeRank : BorelCode → Ordinal.{0}
  | .leaf _ => 0
  | .union f => ⨆ n, (f n).nodeRank + 1
  | .compl c => c.nodeRank + 1

namespace BorelExpression

/-- Enumerate a nonempty set of child numbers, repeating children when it is finite. -/
noncomputable def enumerateChildren (S : Set ℕ) (hn : Nonempty S) : ℕ → S :=
  @Classical.choose (ℕ → S) _ (@exists_surjective_nat S hn _)

theorem enumerateChildren_surjective (S : Set ℕ) (hn : Nonempty S) :
    Function.Surjective (enumerateChildren S hn) :=
  @Classical.choose_spec (ℕ → S) _ (@exists_surjective_nat S hn _)

private theorem enumerate_iUnion {X : Type*} (S : Set ℕ) (hn : Nonempty S) (f : S → Set X) :
    (⋃ n, f (enumerateChildren S hn n)) = ⋃ k, f k := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, h⟩; exact ⟨_, h⟩
  · rintro ⟨k, h⟩
    obtain ⟨n, rfl⟩ := enumerateChildren_surjective S hn k
    exact ⟨n, h⟩

private theorem enumerate_iSup (S : Set ℕ) (hn : Nonempty S) (f : S → Ordinal.{0}) :
    (⨆ n, f (enumerateChildren S hn n)) = ⨆ k, f k := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun n => Ordinal.le_iSup f _
  · apply Ordinal.iSup_le
    intro k
    obtain ⟨n, rfl⟩ := enumerateChildren_surjective S hn k
    exact Ordinal.le_iSup _ n

noncomputable def codeAlgebra : Algebra BorelCode where
  leaf := BorelCode.leaf
  union S hn f := BorelCode.union (fun n => f (enumerateChildren S hn n))
  complement := BorelCode.compl

def setAlgebra {X : Type*} (U : ℕ → Set X) : Algebra (Set X) where
  leaf := U
  union _ _ f := ⋃ k, f k
  complement := compl

noncomputable def levelAlgebra : Algebra Ordinal.{0} where
  leaf _ := 1
  union _ _ f := ⨆ k, f k
  complement α := α + 1

noncomputable def rankAlgebra : Algebra Ordinal.{0} where
  leaf _ := 0
  union _ _ f := ⨆ k, f k + 1
  complement α := α + 1

noncomputable def toCode (c : BorelExpression) (hc : c.Valid) : List ℕ → BorelCode :=
  c.fold hc codeAlgebra

/-- The level is defined directly from the external tree's present children. -/
noncomputable def level (c : BorelExpression) (hc : c.Valid) : List ℕ → Ordinal.{0} :=
  c.fold hc levelAlgebra

/-- The tree rank is defined by the same external recursion, adding one at every edge. -/
noncomputable def nodeRank (c : BorelExpression) (hc : c.Valid) : List ℕ → Ordinal.{0} :=
  c.fold hc rankAlgebra

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Let $C\IncludedIn\omega$ be the nonempty set of subcode numbers of a union, and choose a surjection
    $e:\omega\to C$. For any family of sets $A_k$ and any family of ordinals $\alpha_k$, surjectivity gives
    $$\bigcup_{n\in\omega} A_{e(n)}=\bigcup_{k\in C}A_k,
    \qquad
    \sup_{n\in\omega}\alpha_{e(n)}=\sup_{k\in C}\alpha_k.$$
    For the code level, use the subcodes' levels as $\alpha_k$; for the structural rank, use their ranks plus $1$.
    The leaf and complement clauses are unchanged. Induction on immediate subcodes now proves preservation of all three
    recursively computed values. The enumerations are chosen set-theoretically; no effective choice from a code is asserted.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: lemma
  title: Reindexing the subcodes of a Borel code
-/
theorem toCode_level (c : BorelExpression) (hc : c.Valid) (s : List ℕ) :
    (c.toCode hc s).lvl = c.level hc s := by
  apply map_fold
  · intro n; rfl
  · intro S hn f
    exact enumerate_iSup S hn (fun k => (f k).lvl)
  · intro x; rfl

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: lemma
  title: Reindexing the subcodes of a Borel code
-/
theorem toCode_nodeRank (c : BorelExpression) (hc : c.Valid) (s : List ℕ) :
    (c.toCode hc s).nodeRank = c.nodeRank hc s := by
  apply map_fold
  · intro n; rfl
  · intro S hn f
    exact enumerate_iSup S hn (fun k => (f k).nodeRank + 1)
  · intro x; rfl

private theorem fold_set_eq_evaluate {X : Type*} (c : BorelExpression) (hc : c.Valid)
    (U : ℕ → Set X) (s : List ℕ) (hs : c s ≠ 0) :
    c.fold hc (setAlgebra U) s = c.evaluate hc.2.2.2.2.2 U s := by
  apply c.fold_unique hc (setAlgebra U) (c.evaluate hc.2.2.2.2.2 U) ?_ s hs
  intro t ht
  rw [c.evaluate_isEvaluation hc.2.2.2.2.2 U t]
  unfold foldStep setAlgebra
  by_cases h1 : c t = 1
  · simp [h1, iUnion_subtype]
  · by_cases h2 : c t = 2
    · simp only [h2, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
        ite_false, ite_true, dite_false, dite_true]
      congr 1
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨k, hk, hx⟩
        have he := congrArg Subtype.val (c.complementChild_unique hc t h2 ⟨k, hk⟩)
        change k = (c.complementChild hc t h2).1 at he
        rw [he] at hx
        exact hx
      · intro hx
        exact ⟨_, (c.complementChild hc t h2).2, hx⟩
    · simp [ht, h1, h2]

/-- Re-enumeration preserves the decoded set for every family of basic sets. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: lemma
  title: Reindexing the subcodes of a Borel code
-/
theorem toCode_decode {X : Type*} (c : BorelExpression) (hc : c.Valid)
    (U : ℕ → Set X) (s : List ℕ) (hs : c s ≠ 0) :
    (c.toCode hc s).decode U = c.evaluate hc.2.2.2.2.2 U s := by
  have he : (c.toCode hc s).decode U = c.fold hc (setAlgebra U) s := by
    apply map_fold
    · intro n; rfl
    · intro S hn f
      exact enumerate_iUnion S hn (fun k => (f k).decode U)
    · intro x; rfl
  exact he.trans (fold_set_eq_evaluate c hc U s hs)

/-- The canonical accessibility rank is the supremum over the actual child numbers. -/
theorem accessibility_rank_eq_children (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (hs : c s ≠ 0) :
    (hc.2.2.2.2.2.apply s).rank =
      ⨆ k : Children c s, (hc.2.2.2.2.2.apply (s ++ [k.1])).rank + 1 := by
  rw [Acc.rank_eq]
  simp only [Order.succ_eq_add_one]
  apply le_antisymm
  · apply Ordinal.iSup_le
    rintro ⟨t, _, k, rfl, hk⟩
    exact Ordinal.le_iSup _ (⟨k, hk⟩ : Children c s)
  · apply Ordinal.iSup_le
    intro k
    exact Ordinal.le_iSup
      (fun t : {t // c.Child t s} => (hc.2.2.2.2.2.apply t.1).rank + 1)
      ⟨s ++ [k.1], hs, k.1, rfl, k.2⟩

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Fix a bijection
    $$
    \finseq{\omega}\longrightarrow\omega,\qquad s\longmapsto\FiniteSequenceCode{s}.
    $$
    The natural number $\FiniteSequenceCode{s}$ is the code of the finite sequence $s$ under this fixed bijection.
    We use the concrete list coding constructed in §{sec:lambda-finite-lists} for this bijection.
    Thus corner notation for finite sequences has the same meaning in the classical and computational chapters.

    An external record of a \termuse{Borel code} is a function $c\in\BaireSpace$ whose value
    $c(\FiniteSequenceCode{s})$ records the constructor at position $s$. Use $0$ for an unused position,
    $1$ for a countable union, $2$ for a complement, and $n+3$ for a leaf specifying $U_n$.
    Record the inductive constructors as follows:

    *   For $\BorelLeafCode{n}$ at position $s$, record $n+3$ at $s$; it has no subcodes.

    *   For $\BorelComplementCode{d}$ at position $s$, record $2$ at $s$ and record $d$ starting at $s\concat(0)$.

    *   For $\BorelUnionCode{\Sequence{d_k}{k\in\omega}}$ at position $s$, record $1$ at $s$ and record each $d_k$
        starting at $s\concat(k)$.

    For example, $\BorelComplementCode{\BorelLeafCode{n}}$ has the record
    $$c(\FiniteSequenceCode{\emptyset})=2,\qquad c(\FiniteSequenceCode{\langle0\rangle})=n+3,$$
    with value $0$ at every other position. Thus $\FiniteSequenceCode{s}$ specifies where to look,
    whereas $c(\FiniteSequenceCode{s})$ specifies which constructor is there.

    We also allow the immediate subcodes of a union to be numbered by any nonempty subset of $\omega$,
    and the unique subcode of a complement to have any number. This only changes the indexing of subcodes;
    §{sec:borel-codes-rank} proves that reindexing preserves evaluation and the ordinal measures.
    A position is present when its recorded value is not $0$. A valid record has a present empty position,
    all prefixes of a present position are present, and the leaf, complement, and union cases have respectively
    zero, exactly one, and at least one immediate subcode. In addition, following immediate subcodes cannot continue
    indefinitely. These conditions permit reconstruction by the same inductive rules that define Borel codes.

    To evaluate a record, apply the three evaluation rules from §{sec:borel-codes} to its subcodes.
    Writing $A_s$ for the set represented at a present position $s$, we have:

    *   If $c(\FiniteSequenceCode{s})=n+3$, set $A_s:=U_n$.

    *   If $c(\FiniteSequenceCode{s})=1$, set
        $$A_s:=\bigcup\{A_{s\concat(k)}:c(\FiniteSequenceCode{s\concat(k)})\ne0\}.$$

    *   If $c(\FiniteSequenceCode{s})=2$, with its unique subcode at $s\concat(k)$, set
        $$A_s:=\SetDifference{X}{A_{s\concat(k)}}.$$

    The whole record represents $A_c:=A_\emptyset$. This is the same evaluation of inductive data as before,
    now carried out on the recorded positions.
-/
/-- The operation-based rank agrees with mathlib's canonical rank of the child relation. -/
theorem nodeRank_eq_accessibility_rank (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (hs : c s ≠ 0) : c.nodeRank hc s = (hc.2.2.2.2.2.apply s).rank := by
  apply c.fold_unique hc rankAlgebra (fun t => (hc.2.2.2.2.2.apply t).rank) ?_ s hs
  intro t ht
  rw [accessibility_rank_eq_children c hc t ht]
  unfold foldStep rankAlgebra
  split_ifs with h1 h2
  · rfl
  · dsimp only
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro k
      rw [c.complementChild_unique hc t h2 k]
    · exact Ordinal.le_iSup _ (c.complementChild hc t h2)
  · apply le_antisymm
    · apply Ordinal.iSup_le
      intro k
      exact (k.2 (hc.2.2.1 t (by omega) k.1)).elim
    · exact zero_le

private theorem add_one_lt_omega_one {α : Ordinal.{0}} (h : α < ω₁) : α + 1 < ω₁ := by
  simpa only [Order.succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt h

end BorelExpression

/-- Countable branching keeps every code level below the first uncountable ordinal. -/
theorem BorelCode.lvl_lt_omega_one (c : BorelCode) : c.lvl < ω₁ := by
  induction c with
  | leaf n => exact Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one
  | union f ih => exact Ordinal.iSup_lt_omega_one ih
  | compl c ih => exact BorelExpression.add_one_lt_omega_one ih

theorem BorelCode.nodeRank_lt_omega_one (c : BorelCode) : c.nodeRank < ω₁ := by
  induction c with
  | leaf n =>
    exact (by simp : (0 : Ordinal) < 1).trans
      (Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one)
  | union f ih => exact Ordinal.iSup_lt_omega_one fun n => BorelExpression.add_one_lt_omega_one (ih n)
  | compl c ih => exact BorelExpression.add_one_lt_omega_one ih

namespace BorelExpression

theorem level_lt_omega_one (c : BorelExpression) (hc : c.Valid) (s : List ℕ) : c.level hc s < ω₁ := by
  rw [← toCode_level]
  exact BorelCode.lvl_lt_omega_one _

theorem nodeRank_lt_omega_one (c : BorelExpression) (hc : c.Valid) (s : List ℕ) : c.nodeRank hc s < ω₁ := by
  rw [← toCode_nodeRank]
  exact BorelCode.nodeRank_lt_omega_one _

theorem all_nodeRanks_lt_omega_one (c : BorelExpression) (hc : c.Valid) :
    (⨆ s : List ℕ, c.nodeRank hc s) < ω₁ :=
  Ordinal.iSup_lt_omega_one (c.nodeRank_lt_omega_one hc)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Structural induction shows that $\rho(c)$ is countable for every code $c$: each constructor takes a successor
    or the supremum of countably many countable successors. Regularity of $\omegaOneOrd$ keeps the result countable.
    This explains why the recursive data suffice for the Borel hierarchy up to its stabilization at $\omegaOneOrd$.
-/
/-- The supremum of the canonical ranks of all present nodes is countable. -/
theorem all_accessibility_ranks_lt_omega_one (c : BorelExpression) (hc : c.Valid) :
    (⨆ s : {s : List ℕ // c s ≠ 0}, (hc.2.2.2.2.2.apply s.1).rank) < ω₁ := by
  apply Ordinal.iSup_lt_omega_one
  intro s
  rw [← c.nodeRank_eq_accessibility_rank hc s.1 s.2]
  exact c.nodeRank_lt_omega_one hc s.1

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    To bound the Borel rank of $A_c$, use an ordinal measure adapted to the decoding operations. Define the
    \termdefine{Borel code level} $\ell(c)$ by structural recursion on the code:
    $$
    \begin{aligned}
    \ell(\BorelLeafCode{n}) &= 1,\\
    \ell(\BorelComplementCode{c'}) &= \ell(c') + 1,\\
    \ell(\BorelUnionCode{\Sequence{c_k}{k\in\omega}}) &= \sup_k \ell(c_k).
    \end{aligned}
    $$
    This differs from $\rho$: a union need not increase the code level above the levels of its subcodes.
    The code level gives an upper bound on the Borel rank of the decoded set:
    $$
    A_c \in \bSigma^0_{\ell(c)}(X).
    $$
    The proof is induction on the code, following the three clauses. A leaf decodes to a basic open set, so $A_c \in
    \bSigma^0_1$. A complement decodes to $\SetDifference{X}{A_{c'}}$ with $A_{c'} \in \bSigma^0_{\ell(c')}$; this
    set is $\bPi^0_{\ell(c')}$, hence $\bSigma^0_{\ell(c')+1}$. A union decodes to $\bigcup_k A_{c_k}$ with each
    $A_{c_k} \in \bSigma^0_{\ell(c_k)} \IncludedIn \bSigma^0_{\sup_k \ell(c_k)}$, and each level $\bSigma^0_\gamma$ is
    closed under countable unions, so the union stays at level $\sup_k \ell(c_k)$. Since every $\ell(c)$ is a countable
    ordinal, a countable-rank code always decodes to a Borel set of countable Borel rank.
-/
/-- The existing inductive rank bound now applies to the original external tree. -/
theorem evaluate_mem_borelSigma_level {X : Type*} [MetricSpace X]
    (c : BorelExpression) (hc : c.Valid) (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (s : List ℕ) (hs : c s ≠ 0) :
    c.evaluate hc.2.2.2.2.2 U s ∈ borelSigma (c.level hc s) := by
  rw [← toCode_decode c hc U s hs, ← toCode_level]
  exact BorelCode.decode_mem_borelSigma_lvl hU _

end BorelExpression

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    This reconstructs inductive constructor data from any valid external record, preserving interpretation, level,
    and rank. Conversely, the recording rules in §{sec:borel-codes-encoding} turn inductive data into a valid external
    record. The three evaluation equations show that this preserves the represented set.
    Thus the coding construction and the ordinal bounds apply to the external records as well.
-/
/-- Expand the inductive constructors into the external label syntax. -/
def BorelCode.expression : BorelCode → BorelExpression
  | .leaf n => BorelExpression.basic n
  | .union f => BorelExpression.union (fun n => (f n).expression)
  | .compl c => BorelExpression.complement c.expression

theorem BorelCode.valid_expression (c : BorelCode) : c.expression.Valid := by
  induction c with
  | leaf n => exact BorelExpression.valid_basic n
  | union f ih => exact BorelExpression.valid_union _ ih
  | compl c ih => exact BorelExpression.valid_complement _ ih

theorem BorelCode.denotes_expression {X : Type*} (c : BorelCode) (U : ℕ → Set X) :
    c.expression.denotes c.valid_expression U = c.decode U := by
  induction c with
  | leaf n => exact BorelExpression.denotes_basic U n
  | union f ih =>
    change (BorelExpression.union (fun n => (f n).expression)).denotes
      (BorelExpression.valid_union _ (fun n => (f n).valid_expression)) U = ⋃ n, (f n).decode U
    exact (BorelExpression.denotes_union U _ (fun n => (f n).valid_expression)).trans (iUnion_congr ih)
  | compl c ih =>
    change (BorelExpression.complement c.expression).denotes
      (BorelExpression.valid_complement _ c.valid_expression) U = (c.decode U)ᶜ
    exact (BorelExpression.denotes_complement U _ c.valid_expression).trans (congrArg (fun A : Set X => Aᶜ) ih)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    By the rank stabilization at $\omegaOneOrd$ from §{sec:borel-hierarchy}, every Borel set $A\IncludedIn X$ lies in
    $\bSigma^0_\alpha(X)$ or $\bPi^0_\alpha(X)$ for some $\alpha<\omegaOneOrd$. Construct a code by recursion on $\alpha$:

    *   $\alpha=1$: let $e$ be the empty-set code constructed above. For each $n$, put $c_n:=\BorelLeafCode{n}$ if
        $U_n\IncludedIn A$, and $c_n:=e$ otherwise. Then $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes the open set
        $A$,
        including $A=\emptyset$.
    *   $\alpha>1$, $A\in\bSigma^0_\alpha$: write $A=\bigcup_n B_n$ with $B_n\in\bPi^0_{\beta_n}(X)$ and
        $\beta_n<\alpha$. Recursively choose a code $c_n$ for each $B_n$; then
        $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes $A$.
    *   $A\in\bPi^0_\alpha$: first construct a code $c$ for $\complement A\in\bSigma^0_\alpha$, then use
        $\BorelComplementCode{c}$.

    At a limit ordinal $\lambda$, no extra constructor is needed. The definition of $\bSigma^0_\lambda$ already expresses
    its members as countable unions of sets from classes $\bPi^0_{\beta_n}$ with $\beta_n<\lambda$.
    Thus the same union constructor handles the limit step in the \termuse{Borel hierarchy}.
-/
/-- The external-code existence theorem inherits the book's transfinite construction. -/
theorem exists_external_borel_code {X : Type*} [MetricSpace X]
    (U : ℕ → Set X) (hU : TopologicalSpace.IsTopologicalBasis (range U))
    {A : Set X} (hA : A ∈ borelSigma (ω₁ : Ordinal.{0})) :
    ∃ c : BorelExpression, ∃ hc : c.Valid, c.denotes hc U = A := by
  obtain ⟨d, hd⟩ := BorelCode.exists_decode_eq U hU hA
  exact ⟨d.expression, d.valid_expression, (d.denotes_expression U).trans hd⟩

end PolishSpaceBook
