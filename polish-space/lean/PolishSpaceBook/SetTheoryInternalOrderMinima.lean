module

public import PolishSpaceBook.SetTheoryInitialOrdinalFormulas

@[expose] public section

/-! # The internal subset-minimum clause of a well-order

The subset variable ranges only over sets belonging to the model. No external
well-foundedness of the coded relation is assumed in its interpretation.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

private lemma realize_model_boundedAll (M : ZFSet.{u}) {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : M, y.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs y) :=
  realize_boundedAll (M : ZFClass) i φ xs

def orderSubsetFormula {n : ℕ} (B A : Fin n) : ForcingFormulas.Formula n :=
  boundedAll B (memberAt (Fin.last n) A.castSucc)

def orderNonemptyFormula {n : ℕ} (B : Fin n) : ForcingFormulas.Formula n :=
  boundedExists B (equalAt (Fin.last n) (Fin.last n))

def orderMinimumFormula {n : ℕ} (B R : Fin n) : ForcingFormulas.Formula n :=
  boundedExists B (boundedAll B.castSucc
    (pairMemberFormula R.castSucc.castSucc (Fin.last (n + 1)) (Fin.last n).castSucc).not)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The remaining well-order requirement is the following first-order formula:
    $$\begin{aligned}
    \chi(W,R)\;:\equiv\;\forall B\,\bigl[&
     (B\IncludedIn W\land\exists b\in B\;(b=b))\\
     &\longrightarrow\exists a\in B\,\forall b\in B\;
       \langle b,a\rangle\notin R\bigr].
    \end{aligned}$$
    When interpreted in $M$, the variable $B$ ranges only over sets belonging to $M$.
    We do not assume that every external subset of $W$ belongs to $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation,
    Replacement, and Choice. Let $W,R\in M$. The relation on $W$ coded by $R$ may be arbitrary. Use the subset-minimum
    formula from the ordinal-representation argument:
    $$\begin{aligned}
    \chi(W,R)\;:\equiv\;\forall B\,\bigl[&
     (B\IncludedIn W\land B\ne\emptyset)\\
     &\longrightarrow\exists x\in B\,\forall y\in B\;
     \langle y,x\rangle\notin R\bigr].
    \end{aligned}$$
    In $M\models\chi(W,R)$, only subsets $B$ belonging to $M$ are quantified. Thus external well-foundedness is not
    part of this hypothesis.
-/
def internalOrderMinimaFormula : ForcingFormulas.Formula 2 :=
  (((orderSubsetFormula (2 : Fin 3) 0) ⊓ orderNonemptyFormula 2).imp (orderMinimumFormula 2 1)).all

lemma realize_orderSubsetFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (B A : Fin n) (xs : Fin n → M) :
    (orderSubsetFormula B A).Realize Empty.elim xs ↔ (xs B).val ⊆ (xs A).val := by
  simp only [orderSubsetFormula, realize_model_boundedAll, realize_memberAt_model,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact ⟨fun h x hx => h ⟨x, hM.mem_trans hx (xs B).property⟩ hx, fun h x hx => h hx⟩

lemma realize_orderNonemptyFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (B : Fin n) (xs : Fin n → M) :
    (orderNonemptyFormula B).Realize Empty.elim xs ↔ ∃ b, b ∈ (xs B).val := by
  simp only [orderNonemptyFormula, realize_boundedExists_model, realize_equalAt_model,
    Fin.snoc_last, and_true]
  exact ⟨fun ⟨b, hb⟩ => ⟨b.val, hb⟩, fun ⟨b, hb⟩ => ⟨⟨b, hM.mem_trans hb (xs B).property⟩, hb⟩⟩

lemma realize_orderMinimumFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (B R : Fin n) (xs : Fin n → M) :
    (orderMinimumFormula B R).Realize Empty.elim xs ↔
      ∃ a ∈ (xs B).val, ∀ b ∈ (xs B).val, pair b a ∉ (xs R).val := by
  simp only [orderMinimumFormula, realize_boundedExists_model, realize_model_boundedAll,
    BoundedFormula.realize_not, realize_pairMemberFormula_model hM,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨a, ha, hmin⟩
    exact ⟨a.val, ha, fun b hb => hmin ⟨b, hM.mem_trans hb (xs B).property⟩ hb⟩
  · rintro ⟨a, ha, hmin⟩
    exact ⟨⟨a, hM.mem_trans ha (xs B).property⟩, ha, fun b hb => hmin b.val hb⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation,
    Replacement, and Choice. Let $W,R\in M$. The relation on $W$ coded by $R$ may be arbitrary. Use the subset-minimum
    formula from the ordinal-representation argument:
    $$\begin{aligned}
    \chi(W,R)\;:\equiv\;\forall B\,\bigl[&
     (B\IncludedIn W\land B\ne\emptyset)\\
     &\longrightarrow\exists x\in B\,\forall y\in B\;
     \langle y,x\rangle\notin R\bigr].
    \end{aligned}$$
    In $M\models\chi(W,R)$, only subsets $B$ belonging to $M$ are quantified. Thus external well-foundedness is not
    part of this hypothesis.
-/
lemma realize_internalOrderMinimaFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (A R : M) :
    internalOrderMinimaFormula.Realize Empty.elim ![A, R] ↔
      ∀ B : M, B.val ⊆ A.val → (∃ b, b ∈ B.val) →
        ∃ a ∈ B.val, ∀ b ∈ B.val, pair b a ∉ R.val := by
  simp only [internalOrderMinimaFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, realize_orderSubsetFormula hM, realize_orderNonemptyFormula hM,
    realize_orderMinimumFormula hM]
  change (∀ B : M, (B.val ⊆ A.val ∧ ∃ b, b ∈ B.val) → _) ↔ _
  exact ⟨fun h B hs hn => h B ⟨hs, hn⟩, fun h B hb => h B hb.1 hb.2⟩

end PolishSpaceBook.SetTheoryModels
