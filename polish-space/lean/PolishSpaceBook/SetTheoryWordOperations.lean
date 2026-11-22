module

public import PolishSpaceBook.SetTheoryWordCons
public import PolishSpaceBook.SetTheoryPredicateReflection
public import PolishSpaceBook.SetTheorySequenceExtension
public import Mathlib.Data.List.GetD

@[expose] public section

/-! # First-order recognition of finite-word operations

Lengths, default-zero lookup, initial segments, and one-entry extension are
recognized on the actual finite graphs. These are the operations used by the
finite Borel-certificate tests; no external function graph is assumed internal.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma wordGraph_ext {s t : List ℕ}
    (h : ∀ i v : ℕ, pair (natOrdinal i) (natOrdinal v) ∈ (wordGraph s : ZFSet.{u}) ↔
      pair (natOrdinal i) (natOrdinal v) ∈ (wordGraph t : ZFSet.{u})) : s = t := by
  apply wordGraph_injective.{u}
  ext p
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact (h i.val (s.get i)).mp (mem_wordGraph.mpr ⟨i, rfl⟩)
  · intro hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact (h i.val (t.get i)).mpr (mem_wordGraph.mpr ⟨i, rfl⟩)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Recognition of finite-word operations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    A function graph determines its domain, giving the length assertion.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    These arguments prove
    the external equivalences.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply the principle to finite words. Continue to write $F$ for the internal set of finite word graphs and
    $e(s)$ for the graph of $s$. For a word $s$ and $i\in\omega$, define
    $$r(s,i):=\begin{cases}s(i),&i<|s|,\\0,&|s|\le i.\end{cases}$$
    For any $n\in\omega$, the word $\restrict{s}{n}$ consists of the first $\min(n,|s|)$ entries.
    For $s,t\in F$ and $i,v,n,a\in\omega$, use the following predicate descriptions:
    $$\begin{aligned}
    L(s,n)&:\equiv s:n\to\omega,\\
    R(s,i,v)&:\equiv\langle i,v\rangle\in s\\
     &\qquad{}\lor(v=0\land\forall w\in\omega\;\langle i,w\rangle\notin s),\\
    T(s,n,t)&:\equiv\forall i,v\in\omega\;[\langle i,v\rangle\in t\\
     &\qquad\longleftrightarrow(i\in n\land\langle i,v\rangle\in s)],\\
    J(s,a,t)&:\equiv\exists n,m\in\omega\;[L(s,n)\land L(t,m)\\
     &\qquad{}\land m=n\cup\{n\}\land s\IncludedIn t\land\langle n,a\rangle\in t].
    \end{aligned}$$
-/
lemma wordLength_iff (s : List ℕ) (n : ℕ) :
    IsFunc.{u} (natOrdinal n) Ordinal.omega0.toZFSet (wordGraph s) ↔ n = s.length := by
  constructor
  · intro h
    exact natOrdinal_injective (isFunc_domain_unique h (wordGraph_isFunc s))
  · rintro rfl
    exact wordGraph_isFunc s

/-- Zero is returned precisely when the coordinate is absent, or its value is zero. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply the principle to finite words. Continue to write $F$ for the internal set of finite word graphs and
    $e(s)$ for the graph of $s$. For a word $s$ and $i\in\omega$, define
    $$r(s,i):=\begin{cases}s(i),&i<|s|,\\0,&|s|\le i.\end{cases}$$
    For any $n\in\omega$, the word $\restrict{s}{n}$ consists of the first $\min(n,|s|)$ entries.
    For $s,t\in F$ and $i,v,n,a\in\omega$, use the following predicate descriptions:
    $$\begin{aligned}
    L(s,n)&:\equiv s:n\to\omega,\\
    R(s,i,v)&:\equiv\langle i,v\rangle\in s\\
     &\qquad{}\lor(v=0\land\forall w\in\omega\;\langle i,w\rangle\notin s),\\
    T(s,n,t)&:\equiv\forall i,v\in\omega\;[\langle i,v\rangle\in t\\
     &\qquad\longleftrightarrow(i\in n\land\langle i,v\rangle\in s)],\\
    J(s,a,t)&:\equiv\exists n,m\in\omega\;[L(s,n)\land L(t,m)\\
     &\qquad{}\land m=n\cup\{n\}\land s\IncludedIn t\land\langle n,a\rangle\in t].
    \end{aligned}$$
-/
def SetWordLookup (Ω z s i v : ZFSet.{u}) : Prop :=
  pair i v ∈ s ∨ v = z ∧ ∀ w ∈ Ω, pair i w ∉ s

/-- Parameters omega, zero, word graph, index, value. -/
def wordLookupPredicate : BoundedSetPredicate 5 :=
  .disj (.pairMember 2 3 4) (.conj (.equal 4 1) (.all 0 (.neg (.pairMember 2 3 5))))

def wordLookupFormula : ForcingFormulas.Formula 5 := wordLookupPredicate.compile

lemma realize_wordLookupFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω z s i v : M) :
    wordLookupFormula.Realize Empty.elim ![Ω, z, s, i, v] ↔
      SetWordLookup Ω.val z.val s.val i.val v.val :=
  wordLookupPredicate.realize_compile hM ![Ω, z, s, i, v]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Recognition of finite-word operations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Lookup splits into the cases where the
    coordinate is present and absent.
-/
lemma setWordLookup_iff (s : List ℕ) (i v : ℕ) :
    SetWordLookup.{u} Ordinal.omega0.toZFSet (natOrdinal 0) (wordGraph s)
      (natOrdinal i) (natOrdinal v) ↔ v = s.getD i 0 := by
  simp only [SetWordLookup, forall_mem_omegaOrdinal.{u}, pair_mem_wordGraph.{u},
    natOrdinal_injective.{u}.eq_iff]
  by_cases hi : i < s.length
  · rw [List.getD_eq_getElem s 0 hi]
    simp only [hi, exists_true_left]
    constructor
    · rintro (hv | ⟨_, h⟩)
      · exact hv.symm
      · exact False.elim (h s[i] rfl)
    · intro hv
      exact Or.inl hv.symm
  · rw [List.getD_eq_default s 0 (Nat.le_of_not_gt hi)]
    simp [hi]

/-- Restriction to the first n coordinates, including n beyond the word length. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply the principle to finite words. Continue to write $F$ for the internal set of finite word graphs and
    $e(s)$ for the graph of $s$. For a word $s$ and $i\in\omega$, define
    $$r(s,i):=\begin{cases}s(i),&i<|s|,\\0,&|s|\le i.\end{cases}$$
    For any $n\in\omega$, the word $\restrict{s}{n}$ consists of the first $\min(n,|s|)$ entries.
    For $s,t\in F$ and $i,v,n,a\in\omega$, use the following predicate descriptions:
    $$\begin{aligned}
    L(s,n)&:\equiv s:n\to\omega,\\
    R(s,i,v)&:\equiv\langle i,v\rangle\in s\\
     &\qquad{}\lor(v=0\land\forall w\in\omega\;\langle i,w\rangle\notin s),\\
    T(s,n,t)&:\equiv\forall i,v\in\omega\;[\langle i,v\rangle\in t\\
     &\qquad\longleftrightarrow(i\in n\land\langle i,v\rangle\in s)],\\
    J(s,a,t)&:\equiv\exists n,m\in\omega\;[L(s,n)\land L(t,m)\\
     &\qquad{}\land m=n\cup\{n\}\land s\IncludedIn t\land\langle n,a\rangle\in t].
    \end{aligned}$$
-/
def SetWordTake (Ω s n t : ZFSet.{u}) : Prop :=
  ∀ i ∈ Ω, ∀ v ∈ Ω, pair i v ∈ t ↔ i ∈ n ∧ pair i v ∈ s

/-- Parameters omega, source word, cutoff, target word. -/
def wordTakePredicate : BoundedSetPredicate 4 :=
  .all 0 (.all 0 (.iff (.pairMember 3 4 5) (.conj (.member 4 2) (.pairMember 1 4 5))))

def wordTakeFormula : ForcingFormulas.Formula 4 := wordTakePredicate.compile

lemma realize_wordTakeFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω s n t : M) :
    wordTakeFormula.Realize Empty.elim ![Ω, s, n, t] ↔ SetWordTake Ω.val s.val n.val t.val :=
  wordTakePredicate.realize_compile hM ![Ω, s, n, t]

lemma pair_mem_wordGraph_take (s : List ℕ) (n i v : ℕ) :
    pair (natOrdinal i) (natOrdinal v) ∈ (wordGraph (s.take n) : ZFSet.{u}) ↔
      i < n ∧ pair (natOrdinal i) (natOrdinal v) ∈ wordGraph s := by
  simp only [pair_mem_wordGraph, List.length_take, Nat.lt_min]
  constructor
  · rintro ⟨⟨hin, his⟩, hv⟩
    exact ⟨hin, his, by simpa using hv⟩
  · rintro ⟨hin, his, hv⟩
    exact ⟨⟨hin, his⟩, by simpa using hv⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Recognition of finite-word operations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Restriction retains exactly the pairs whose first coordinate is below the
    cutoff; equality of all pairs gives equality of the finite words.
-/
lemma setWordTake_iff (s t : List ℕ) (n : ℕ) :
    SetWordTake.{u} Ordinal.omega0.toZFSet (wordGraph s) (natOrdinal n) (wordGraph t) ↔
      t = s.take n := by
  simp only [SetWordTake, forall_mem_omegaOrdinal.{u}, natOrdinal_mem_natOrdinal.{u}]
  constructor
  · intro h
    exact wordGraph_ext.{u} (fun i v => (h i v).trans (pair_mem_wordGraph_take.{u} s n i v).symm)
  · rintro rfl
    exact pair_mem_wordGraph_take.{u} s n

/-- Append one specified value; the function-graph clauses fix both lengths. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We apply the principle to finite words. Continue to write $F$ for the internal set of finite word graphs and
    $e(s)$ for the graph of $s$. For a word $s$ and $i\in\omega$, define
    $$r(s,i):=\begin{cases}s(i),&i<|s|,\\0,&|s|\le i.\end{cases}$$
    For any $n\in\omega$, the word $\restrict{s}{n}$ consists of the first $\min(n,|s|)$ entries.
    For $s,t\in F$ and $i,v,n,a\in\omega$, use the following predicate descriptions:
    $$\begin{aligned}
    L(s,n)&:\equiv s:n\to\omega,\\
    R(s,i,v)&:\equiv\langle i,v\rangle\in s\\
     &\qquad{}\lor(v=0\land\forall w\in\omega\;\langle i,w\rangle\notin s),\\
    T(s,n,t)&:\equiv\forall i,v\in\omega\;[\langle i,v\rangle\in t\\
     &\qquad\longleftrightarrow(i\in n\land\langle i,v\rangle\in s)],\\
    J(s,a,t)&:\equiv\exists n,m\in\omega\;[L(s,n)\land L(t,m)\\
     &\qquad{}\land m=n\cup\{n\}\land s\IncludedIn t\land\langle n,a\rangle\in t].
    \end{aligned}$$
-/
def SetWordSnoc (Ω s a t : ZFSet.{u}) : Prop :=
  ∃ n ∈ Ω, ∃ m ∈ Ω, IsFunc n Ω s ∧ IsFunc m Ω t ∧
    m = insert n n ∧ s ⊆ t ∧ pair n a ∈ t

/-- Parameters omega, source word, appended value, target word. -/
def wordSnocPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.ex 0 (.conj (.function 4 0 1) (.conj (.function 5 0 3)
    (.conj (.successor 5 4) (.conj (.subset 1 3) (.pairMember 3 4 2))))))

def wordSnocFormula : ForcingFormulas.Formula 4 := wordSnocPredicate.compile

lemma realize_wordSnocFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (Ω s a t : M) :
    wordSnocFormula.Realize Empty.elim ![Ω, s, a, t] ↔ SetWordSnoc Ω.val s.val a.val t.val :=
  wordSnocPredicate.realize_compile hM ![Ω, s, a, t]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Recognition of finite-word operations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For extension, the two function conditions
    fix the lengths, inclusion fixes the prefix, and the last pair fixes the appended entry.
-/
lemma setWordSnoc_iff (s t : List ℕ) (a : ℕ) :
    SetWordSnoc.{u} Ordinal.omega0.toZFSet (wordGraph s) (natOrdinal a) (wordGraph t) ↔
      t = s ++ [a] := by
  constructor
  · rintro ⟨n, hn, m, hm, hs, ht, hsucc, hsub, hlast⟩
    have hn' := isFunc_domain_unique hs (wordGraph_isFunc s)
    obtain ⟨b, rfl⟩ := immediateWordExtension_iff.mp ⟨n, hn, m, hm, hs, ht, hsucc, hsub⟩
    rw [hn', pair_mem_wordGraph] at hlast
    have hab : b = a := by simpa using hlast.2
    rw [hab]
  · rintro rfl
    obtain ⟨n, hn, m, hm, hs, ht, hsucc, hsub⟩ :=
      immediateWordExtension_iff.mpr (show ∃ k, s ++ [a] = s ++ [k] from ⟨a, rfl⟩)
    refine ⟨n, hn, m, hm, hs, ht, hsucc, hsub, ?_⟩
    rw [isFunc_domain_unique hs (wordGraph_isFunc s), pair_mem_wordGraph]
    exact ⟨by simp, by simp⟩

end PolishSpaceBook.SetTheoryModels
