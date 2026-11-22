module

public import PolishSpaceBook.BorelSetCodes

@[expose] public section

/-! # First-order definitions of live children and true leaves -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

def liveLabelPredicate {n : ℕ} (Ω l z s : Fin n) : BoundedSetPredicate n :=
  .ex Ω (.conj (.pairMember l.castSucc s.castSucc (Fin.last n))
    (.neg (.equal (Fin.last n) z.castSucc)))

def liveLabelFormula {n : ℕ} (Ω l z s : Fin n) : ForcingFormulas.Formula n :=
  (liveLabelPredicate Ω l z s).compile

lemma realize_liveLabelFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (Ω l z s : Fin n) (xs : Fin n → M) :
    (liveLabelFormula Ω l z s).Realize Empty.elim xs ↔
      ∃ a ∈ (xs Ω).val, pair (xs s).val a ∈ (xs l).val ∧ a ≠ (xs z).val := by
  rw [liveLabelFormula, BoundedSetPredicate.realize_compile hM]
  simp only [liveLabelPredicate, BoundedSetPredicate.eval, Fin.snoc_last,
    Fin.snoc_castSucc, Function.comp_apply]

def liveChildPredicate {n : ℕ} (Ω l z t s : Fin n) : BoundedSetPredicate n :=
  .conj (immediateWordPredicate Ω t s)
    (.conj (liveLabelPredicate Ω l z t) (liveLabelPredicate Ω l z s))

lemma eval_liveChildPredicate {n : ℕ} (Ω l z t s : Fin n) (xs : Fin n → ZFSet.{u})
    (hΩ : xs Ω = Ordinal.omega0.toZFSet) (hz : xs z = natOrdinal 0) :
    (liveChildPredicate Ω l z t s).eval xs ↔ LiveChild (xs l) (xs t) (xs s) := by
  simp only [liveChildPredicate, BoundedSetPredicate.eval, eval_immediateWordPredicate _ _ _ _ hΩ,
    liveLabelPredicate, Fin.snoc_last, Fin.snoc_castSucc, hΩ, hz, LiveChild]

def liveChildFormula {n : ℕ} (Ω l z t s : Fin n) : ForcingFormulas.Formula n :=
  (liveChildPredicate Ω l z t s).compile

lemma realize_liveChildFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (Ω l z t s : Fin n) (xs : Fin n → M)
    (hΩ : (xs Ω).val = Ordinal.omega0.toZFSet) (hz : (xs z).val = natOrdinal 0) :
    (liveChildFormula Ω l z t s).Realize Empty.elim xs ↔
      LiveChild (xs l).val (xs t).val (xs s).val :=
  ((liveChildPredicate Ω l z t s).realize_compile hM xs).trans
    (eval_liveChildPredicate Ω l z t s (Subtype.val ∘ xs) hΩ hz)

/-- Three successors represent the offset used by a leaf label. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Here the offset relation is a first-order set-theoretic formula: with
    $$S(a,b):\equiv b=a\cup\{a\},$$
    replace $m=n+3$ by
    $$\exists a\,\exists d\;(S(n,a)\land S(a,d)\land S(d,m)).$$
-/
def threeSuccessorsFormula {n : ℕ} (a b : Fin n) : ForcingFormulas.Formula n :=
  (successorFormula (Fin.last n).castSucc a.castSucc.castSucc ⊓
    (successorFormula (Fin.last (n + 1)) (Fin.last n).castSucc ⊓
      successorFormula b.castSucc.castSucc (Fin.last (n + 1)))).ex.ex

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    By transitivity, each successor equation recognizes the actual set operation. Hence any internal witnesses
    must satisfy $a=n+1$, $d=n+2$, and $m=n+3$. Conversely, when $m=n+3$, choose $a=n+1$ and $d=n+2$;
    these intermediate ordinals belong to $M$ by Pairing and Union. Thus the internal formula has exactly the
    displayed meaning.
-/
lemma realize_threeSuccessorsFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {n : ℕ} (a b : Fin n) (xs : Fin n → M) {k : ℕ} (ha : (xs a).val = natOrdinal k) :
    (threeSuccessorsFormula a b).Realize Empty.elim xs ↔ (xs b).val = natOrdinal (k + 3) := by
  have hs {m : ℕ} (a b : Fin m) (ys : Fin m → M) :
      (successorFormula a b).Realize Empty.elim ys ↔ (ys a).val = insert (ys b).val (ys b).val :=
    realize_successorFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) a b ys
  simp only [threeSuccessorsFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    hs, Fin.snoc_last, Fin.snoc_castSucc, ha]
  have hnext {a : ZFSet.{u}} (ha : a ∈ M) : insert a a ∈ M := by
    rw [ZFSet.insert_eq]
    exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair ha) ha
  constructor
  · rintro ⟨v, w, hv, hw, hb⟩
    simpa only [natOrdinal_succ, hv, hw] using hb
  · intro hb
    have hkM : natOrdinal k ∈ M := ha ▸ (xs a).property
    have hk1M : natOrdinal (k + 1) ∈ M := natOrdinal_succ k ▸ hnext hkM
    have hk2M : natOrdinal (k + 2) ∈ M := natOrdinal_succ (k + 1) ▸ hnext hk1M
    exact ⟨⟨natOrdinal (k + 1), hk1M⟩, ⟨natOrdinal (k + 2), hk2M⟩,
      natOrdinal_succ k, natOrdinal_succ (k + 1), hb.trans (natOrdinal_succ (k + 2))⟩

def trueLeafFormula {n : ℕ} (Ω T l b x s : Fin n) : ForcingFormulas.Formula n :=
  boundedExists Ω (boundedExists Ω.castSucc
    (threeSuccessorsFormula (Fin.last n).castSucc (Fin.last (n + 1)) ⊓
      (pairMemberFormula l.castSucc.castSucc s.castSucc.castSucc (Fin.last (n + 1)) ⊓
        boundedExists T.castSucc.castSucc
          (pairMemberFormula b.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc (Fin.last (n + 2)) ⊓
            orderSubsetFormula (Fin.last (n + 2)) x.castSucc.castSucc.castSucc))))

lemma realize_trueLeafFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {n : ℕ} (Ω T l b x s : Fin n) (xs : Fin n → M)
    (hΩ : (xs Ω).val = Ordinal.omega0.toZFSet) (hT : (xs T).val = finiteSequences) :
    (trueLeafFormula Ω T l b x s).Realize Empty.elim xs ↔
      TrueLeaf (xs l).val (xs b).val (xs x).val (xs s).val := by
  simp only [trueLeafFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
    realize_pairMemberFormula_model hM, realize_orderSubsetFormula hM,
    Fin.snoc_last, Fin.snoc_castSucc, hΩ, hT]
  constructor
  · rintro ⟨a, ha, v, _, hv, hl, w, hw, hb, hx⟩
    obtain ⟨k, hk⟩ := mem_omegaOrdinal.mp ha
    have he := (realize_threeSuccessorsFormula hM hpair hunion _ _ _
      (by simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hk.symm)).mp hv
    have he' : v.val = natOrdinal (k + 3) := by simpa only [Fin.snoc_last] using he
    exact ⟨k, he' ▸ hl, w.val, hw, by simpa only [hk] using hb, hx⟩
  · rintro ⟨k, hl, w, hw, hb, hx⟩
    have homega : Ordinal.omega0.toZFSet ∈ M := hΩ ▸ (xs Ω).property
    let a : M := ⟨natOrdinal k, hM.mem_trans (mem_omegaOrdinal.mpr ⟨k, rfl⟩) homega⟩
    let v : M := ⟨natOrdinal (k + 3), hM.mem_trans (mem_omegaOrdinal.mpr ⟨k + 3, rfl⟩) homega⟩
    let wM : M := ⟨w, hM.mem_trans hw (hT ▸ (xs T).property)⟩
    refine ⟨a, mem_omegaOrdinal.mpr ⟨k, rfl⟩, v, mem_omegaOrdinal.mpr ⟨k + 3, rfl⟩,
      ?_, hl, wM, hw, hb, hx⟩
    apply (realize_threeSuccessorsFormula hM hpair hunion _ _ _ (k := k)
      (by simp only [Fin.snoc_castSucc, Fin.snoc_last, a])).mpr
    simp only [Fin.snoc_last, v]

end PolishSpaceBook.BorelExpression
