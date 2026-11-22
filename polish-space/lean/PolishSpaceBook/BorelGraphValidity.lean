module

public import PolishSpaceBook.BorelInternalParameters
public import PolishSpaceBook.SetTheoryPredicateReflection
public import PolishSpaceBook.SetTheoryInternalRelationRanks

@[expose] public section

/-! # Recognizing Borel syntax from set-coded label graphs -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

lemma labelGraph_isFunc (c : BorelExpression) :
    IsFunc (finiteSequences : ZFSet.{u}) Ordinal.omega0.toZFSet c.labelGraph := by
  constructor
  · intro p hp
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨mem_finiteSequences.mpr ⟨s, rfl⟩,
      mem_omegaOrdinal.mpr ⟨c s, rfl⟩⟩
  · intro s hs
    obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hs
    exact ⟨natOrdinal (c w), (pair_mem_labelGraph c w _).mpr rfl,
      fun y hy => (pair_mem_labelGraph c w y).mp hy⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Local recognition of Borel label graphs
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Read $c(s)$ from the unique value of $\ell$ at $e(s)$. Every element of $T$ is the graph of exactly one finite
    word, so this recovers the entire graph, and the labels determine $c$ uniquely.
    For word graphs, $J(e(t),e(s))$ means $t=s\concat\langle k\rangle$ for some $k$.
    Distinct $k$ give distinct children. Substituting this characterization into the five displayed rules gives
    exactly the root, prefix, leaf, union, and complement clauses for the expression.
-/
lemma labelGraph_injective : Function.Injective (labelGraph : BorelExpression → ZFSet.{u}) := by
  intro c d h
  funext s
  apply natOrdinal_injective.{u}
  apply (pair_mem_labelGraph d s _).mp
  rw [← h]
  exact (pair_mem_labelGraph c s _).mpr rfl

/-- Every total natural-valued graph on finite words decodes to exactly those labels. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Local recognition of Borel label graphs
-/
theorem exists_labelGraph_of_isFunc {l : ZFSet.{u}}
    (hl : IsFunc finiteSequences Ordinal.omega0.toZFSet l) :
    ∃ c : BorelExpression, c.labelGraph = l := by
  have hex (s : List ℕ) : ∃ n : ℕ, pair (wordGraph s) (natOrdinal n) ∈ l := by
    obtain ⟨y, hy, _⟩ := hl.2 _ (mem_finiteSequences.mpr ⟨s, rfl⟩)
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp (ZFSet.pair_mem_prod.mp (hl.1 hy)).2
    exact ⟨n, hy⟩
  choose c hc using hex
  refine ⟨c, ZFSet.ext fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hp
    exact hc s
  · intro hp
    obtain ⟨s, hs, y, _, rfl⟩ := ZFSet.mem_prod.mp (hl.1 hp)
    obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hs
    exact (pair_mem_labelGraph c w y).mpr
      ((hl.2 _ (mem_finiteSequences.mpr ⟨w, rfl⟩)).unique hp (hc w))

/-- Immediate extension, expressed using the shared bounded-predicate compiler. -/
def immediateAt {n : ℕ} (Ω t s : Fin n) : BoundedSetPredicate n :=
  .ex Ω (.ex Ω.castSucc (.conj (.function (Fin.last n).castSucc Ω.castSucc.castSucc s.castSucc.castSucc)
    (.conj (.function (Fin.last (n + 1)) Ω.castSucc.castSucc t.castSucc.castSucc)
      (.conj (.successor (Fin.last (n + 1)) (Fin.last n).castSucc)
        (.subset s.castSucc.castSucc t.castSucc.castSucc)))))

lemma eval_immediateAt {n : ℕ} (Ω t s : Fin n) (xs : Fin n → ZFSet.{u})
    (hΩ : xs Ω = Ordinal.omega0.toZFSet) :
    (immediateAt Ω t s).eval xs ↔ ImmediateWordExtension (xs t) (xs s) := by
  simp only [immediateAt, eval, Fin.snoc_last, Fin.snoc_castSucc, hΩ, ImmediateWordExtension]

/-- A nonzero immediate child; the parent's label is deliberately unrestricted. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $L(\ell)$ assert the following local rules, with all node variables ranging over $T$:

    * $\ell(e(\emptyset))\ne0$.
    * If $J(t,s)$ and $\ell(t)\ne0$, then $\ell(s)\ne0$.
    * If $\ell(s)\notin\{0,1,2\}$ and $J(t,s)$, then $\ell(t)=0$.
    * If $\ell(s)=1$, there is $t$ with $J(t,s)$ and $\ell(t)\ne0$.
    * If $\ell(s)=2$, there is exactly one such $t$.

    These are bounded conditions: each label test is membership of an ordered pair in $\ell$, and the
    immediate-extension test is bounded as well.
-/
def syntaxChildAt {n : ℕ} (Ω l z t s : Fin n) : BoundedSetPredicate n :=
  .conj (immediateAt Ω t s) (.neg (.pairMember l t z))

lemma eval_syntaxChildAt {n : ℕ} (Ω l z t s : Fin n) (xs : Fin n → ZFSet.{u})
    (c : BorelExpression) (v w : List ℕ) (hΩ : xs Ω = Ordinal.omega0.toZFSet)
    (hl : xs l = c.labelGraph) (hz : xs z = natOrdinal 0)
    (ht : xs t = wordGraph v) (hs : xs s = wordGraph w) :
    (syntaxChildAt Ω l z t s).eval xs ↔ (∃ k, v = w ++ [k]) ∧ c v ≠ 0 := by
  simp only [syntaxChildAt, eval, eval_immediateAt Ω t s xs hΩ, ht, hs, hl, hz,
    immediateWordExtension_iff, pair_mem_labelGraph, natOrdinal_injective.eq_iff, ne_comm]

/-- Parameters omega, words, zero, one, two, root word, label graph. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $L(\ell)$ assert the following local rules, with all node variables ranging over $T$:

    * $\ell(e(\emptyset))\ne0$.
    * If $J(t,s)$ and $\ell(t)\ne0$, then $\ell(s)\ne0$.
    * If $\ell(s)\notin\{0,1,2\}$ and $J(t,s)$, then $\ell(t)=0$.
    * If $\ell(s)=1$, there is $t$ with $J(t,s)$ and $\ell(t)\ne0$.
    * If $\ell(s)=2$, there is exactly one such $t$.

    These are bounded conditions: each label test is membership of an ordered pair in $\ell$, and the
    immediate-extension test is bounded as well.
-/
def localShapePredicate : BoundedSetPredicate 7 :=
  .conj (.neg (.pairMember 6 5 2)) (.all 1
    (.conj (.all 1 (.disj (.neg (syntaxChildAt 0 6 2 8 7)) (.neg (.pairMember 6 7 2))))
      (.conj (.disj (.disj (.pairMember 6 7 2) (.disj (.pairMember 6 7 3) (.pairMember 6 7 4)))
        (.neg (.ex 1 (syntaxChildAt 0 6 2 8 7))))
        (.conj (.disj (.neg (.pairMember 6 7 3)) (.ex 1 (syntaxChildAt 0 6 2 8 7)))
          (.disj (.neg (.pairMember 6 7 4)) (.ex 1 (.conj (syntaxChildAt 0 6 2 8 7)
            (.all 1 (.disj (.neg (syntaxChildAt 0 6 2 9 7)) (.equal 9 8))))))))))

lemma forall_mem_finiteSequences (P : ZFSet.{u} → Prop) :
    (∀ s ∈ finiteSequences, P s) ↔ ∀ w : List ℕ, P (wordGraph w) := by
  exact ⟨fun h w => h _ (mem_finiteSequences.mpr ⟨w, rfl⟩),
    fun h s hs => by obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hs; exact h w⟩

lemma exists_mem_finiteSequences (P : ZFSet.{u} → Prop) :
    (∃ s ∈ finiteSequences, P s) ↔ ∃ w : List ℕ, P (wordGraph w) := by
  exact ⟨fun ⟨s, hs, hp⟩ => by obtain ⟨w, rfl⟩ := mem_finiteSequences.mp hs; exact ⟨w, hp⟩,
    fun ⟨w, hp⟩ => ⟨_, mem_finiteSequences.mpr ⟨w, rfl⟩, hp⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Local recognition of Borel label graphs
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $L(\ell)$ assert the following local rules, with all node variables ranging over $T$:

    * $\ell(e(\emptyset))\ne0$.
    * If $J(t,s)$ and $\ell(t)\ne0$, then $\ell(s)\ne0$.
    * If $\ell(s)\notin\{0,1,2\}$ and $J(t,s)$, then $\ell(t)=0$.
    * If $\ell(s)=1$, there is $t$ with $J(t,s)$ and $\ell(t)\ne0$.
    * If $\ell(s)=2$, there is exactly one such $t$.

    These are bounded conditions: each label test is membership of an ordered pair in $\ell$, and the
    immediate-extension test is bounded as well.
-/
lemma eval_localShapePredicate (c : BorelExpression) :
    localShapePredicate.eval ![(Ordinal.omega0.toZFSet : ZFSet.{u}), finiteSequences,
      natOrdinal 0, natOrdinal 1, natOrdinal 2, wordGraph [], c.labelGraph] ↔
      c [] ≠ 0 ∧ (∀ s k, c (s ++ [k]) ≠ 0 → c s ≠ 0) ∧
      (∀ s, 3 ≤ c s → ∀ k, c (s ++ [k]) = 0) ∧
      (∀ s, c s = 1 → ∃ k, c (s ++ [k]) ≠ 0) ∧
      (∀ s, c s = 2 → ∃! k, c (s ++ [k]) ≠ 0) := by
  classical
  have hj (s t : List ℕ) :
      (immediateAt (0 : Fin 9) 8 7).eval (Fin.snoc (Fin.snoc
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), finiteSequences, natOrdinal 0, natOrdinal 1,
          natOrdinal 2, wordGraph [], c.labelGraph] (wordGraph s)) (wordGraph t)) ↔
        ∃ k, t = s ++ [k] :=
    (eval_immediateAt _ _ _ _ rfl).trans immediateWordExtension_iff
  have hj' (s v t : List ℕ) :
      (immediateAt (0 : Fin 10) 9 7).eval (Fin.snoc (Fin.snoc (Fin.snoc
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), finiteSequences, natOrdinal 0, natOrdinal 1,
          natOrdinal 2, wordGraph [], c.labelGraph] (wordGraph s)) (wordGraph v)) (wordGraph t)) ↔
        ∃ k, t = s ++ [k] :=
    (eval_immediateAt _ _ _ _ rfl).trans immediateWordExtension_iff
  have hn (k : ℕ) : (¬0 = k) ↔ k ≠ 0 := ne_comm
  simp only [localShapePredicate, syntaxChildAt, eval]
  dsimp [Fin.snoc, Fin.castPred, Fin.castLT]
  simp only [forall_mem_finiteSequences, exists_mem_finiteSequences, hj, hj',
    pair_mem_labelGraph, natOrdinal_injective.eq_iff,
    wordGraph_injective.eq_iff, hn]
  constructor
  · rintro ⟨hroot, h⟩
    refine ⟨hroot, ?_, ?_, ?_, ?_⟩
    · intro s k hk
      exact ((h s).1 (s ++ [k])).resolve_left (by exact not_not.mpr ⟨⟨k, rfl⟩, hk⟩)
    · intro s hs k
      have hn := (h s).2.1.resolve_left (by omega)
      by_contra hk
      exact hn ⟨s ++ [k], ⟨k, rfl⟩, hk⟩
    · intro s hs
      obtain ⟨v, ⟨k, rfl⟩, hk⟩ := (h s).2.2.1.resolve_left (by simpa using hs.symm)
      exact ⟨k, hk⟩
    · intro s hs
      obtain ⟨v, ⟨⟨k, rfl⟩, hk⟩, hu⟩ := (h s).2.2.2.resolve_left (by simpa using hs.symm)
      refine ⟨k, hk, fun i hi => ?_⟩
      have he := (hu (s ++ [i])).resolve_left (by exact not_not.mpr ⟨⟨i, rfl⟩, hi⟩)
      simpa using he
  · rintro ⟨hroot, hp, hl, hu, hc⟩
    refine ⟨hroot, fun s => ⟨?_, ?_, ?_, ?_⟩⟩
    · intro v
      by_cases hv : (∃ k, v = s ++ [k]) ∧ c v ≠ 0
      · obtain ⟨⟨k, rfl⟩, hk⟩ := hv
        exact Or.inr (hp s k hk)
      · exact Or.inl hv
    · by_cases hs : 3 ≤ c s
      · right
        rintro ⟨v, ⟨k, rfl⟩, hk⟩
        exact hk (hl s hs k)
      · left; omega
    · by_cases hs : c s = 1
      · obtain ⟨k, hk⟩ := hu s hs
        exact Or.inr ⟨s ++ [k], ⟨k, rfl⟩, hk⟩
      · exact Or.inl (Ne.symm hs)
    · by_cases hs : c s = 2
      · obtain ⟨k, hk, huniq⟩ := hc s hs
        refine Or.inr ⟨s ++ [k], ⟨⟨k, rfl⟩, hk⟩, fun v => ?_⟩
        by_cases hv : (∃ i, v = s ++ [i]) ∧ c v ≠ 0
        · obtain ⟨⟨i, rfl⟩, hi⟩ := hv
          exact Or.inr (by rw [huniq i hi])
        · exact Or.inl hv
      · exact Or.inl (Ne.symm hs)

end PolishSpaceBook.BorelExpression
