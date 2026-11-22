module

public import PolishSpaceBook.SetTheoryInternalRecursion

@[expose] public section

/-! # A bounded definition of the finite von Neumann ordinals -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

abbrev natOrdinal (n : ℕ) : ZFSet.{u} := (n : Ordinal.{u}).toZFSet

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
lemma natOrdinal_zero : natOrdinal 0 = (∅ : ZFSet.{u}) := Ordinal.toZFSet_zero

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
lemma natOrdinal_succ (n : ℕ) :
    natOrdinal (n + 1) = insert (natOrdinal n) (natOrdinal n) := by
  simp only [natOrdinal, Nat.cast_add, Nat.cast_one, Ordinal.toZFSet_add_one]

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
lemma mem_natOrdinal {z : ZFSet.{u}} {n : ℕ} :
    z ∈ natOrdinal n ↔ ∃ m < n, natOrdinal m = z := by
  rw [Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp (ha.trans (Ordinal.natCast_lt_omega0 n))
    exact ⟨m, by exact_mod_cast ha, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, by exact_mod_cast hm, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
lemma mem_omegaOrdinal {z : ZFSet.{u}} :
    z ∈ Ordinal.omega0.toZFSet ↔ ∃ n, natOrdinal n = z := by
  rw [Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, rfl⟩

/-- The successor x = y ∪ {y}, with every quantifier bounded by x or y. -/
def successorFormula {n : ℕ} (x y : Fin n) : ForcingFormulas.Formula n :=
  memberAt y x ⊓ boundedAll y (memberAt (Fin.last n) x.castSucc) ⊓
    boundedAll x (equalAt (Fin.last n) y.castSucc ⊔ memberAt (Fin.last n) y.castSucc)

lemma successorFormula_deltaZero {n : ℕ} (x y : Fin n) : IsDeltaZero (successorFormula x y) :=
  ((memberAt_deltaZero _ _).and (.all y (memberAt_deltaZero _ _))).and
    (.all x ((equalAt_deltaZero _ _).or (memberAt_deltaZero _ _)))

def zeroOrSuccessorFormula {n : ℕ} (x : Fin n) : ForcingFormulas.Formula n :=
  boundedAll x ⊥ ⊔ boundedExists x (successorFormula x.castSucc (Fin.last n))

lemma zeroOrSuccessorFormula_deltaZero {n : ℕ} (x : Fin n) :
    IsDeltaZero (zeroOrSuccessorFormula x) :=
  (IsDeltaZero.all x .falsum).or (.exists x (successorFormula_deltaZero _ _))

/-- An ordinal, itself and all of whose elements are zero or successors. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    To separate precisely its finite ordinals, put
    $$\begin{aligned}
    \mathrm{ZS}(y)&:\equiv y=\emptyset\lor\exists z\in y\,(y=z\cup\{z\}),\\
    \mathrm{FinOrd}(y)&:\equiv\mathrm{Ord}(y)\land\mathrm{ZS}(y)
     \land\forall z\in y\,\mathrm{ZS}(z).
    \end{aligned}$$
-/
def finiteOrdinalFormula {n : ℕ} (x : Fin n) : ForcingFormulas.Formula n :=
  ordinalFormula x ⊓ zeroOrSuccessorFormula x ⊓ boundedAll x (zeroOrSuccessorFormula (Fin.last n))

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    These are bounded formulas: emptiness says that there is no member, and the successor equality expands as
    $$z\in y\land(\forall w\in z\,w\in y)
     \land\forall w\in y\,(w=z\lor w\in z).$$
-/
lemma finiteOrdinalFormula_deltaZero {n : ℕ} (x : Fin n) : IsDeltaZero (finiteOrdinalFormula x) :=
  ((ordinalFormula_deltaZero x).and (zeroOrSuccessorFormula_deltaZero x)).and
    (.all x (zeroOrSuccessorFormula_deltaZero _))

lemma realize_successorFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x y : Fin n) (xs : Fin n → ClassDomain C) :
    (successorFormula x y).Realize Empty.elim xs ↔ (xs x).val = insert (xs y).val (xs y).val := by
  simp only [successorFormula, BoundedFormula.realize_inf, realize_boundedAll,
    BoundedFormula.realize_sup, realize_memberAt_class, realize_equalAt_class,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨⟨hyx, hsub⟩, h⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases h ⟨z, hC _ (xs x).property _ hz⟩ hz with he | hm
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr hm
    · rintro (rfl | hz)
      · exact hyx
      · exact hsub ⟨z, hC _ (xs y).property _ hz⟩ hz
  · intro he
    constructor
    · constructor
      · rw [he]; exact ZFSet.mem_insert _ _
      · intro z hz; rw [he]; exact ZFSet.mem_insert_iff.mpr (Or.inr hz)
    · intro z hz
      rw [he, ZFSet.mem_insert_iff] at hz
      exact hz.imp (fun h => Subtype.ext h) id

lemma realize_zeroOrSuccessorFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x : Fin n) (xs : Fin n → ClassDomain C) :
    (zeroOrSuccessorFormula x).Realize Empty.elim xs ↔
      (xs x).val = ∅ ∨ ∃ y ∈ (xs x).val, (xs x).val = insert y y := by
  simp only [zeroOrSuccessorFormula, BoundedFormula.realize_sup, realize_boundedAll,
    BoundedFormula.realize_bot, realize_boundedExists, realize_successorFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro (h | ⟨y, hy, he⟩)
    · left
      apply ZFSet.ext
      intro z
      exact ⟨fun hz => False.elim (h ⟨z, hC _ (xs x).property _ hz⟩ hz),
        fun hz => False.elim (ZFSet.notMem_empty _ hz)⟩
    · exact Or.inr ⟨y.val, hy, he⟩
  · rintro (he | ⟨y, hy, he⟩)
    · left; intro z hz; exact ZFSet.notMem_empty _ (he ▸ hz)
    · exact Or.inr ⟨⟨y, hC _ (xs x).property _ hy⟩, hy, he⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Every finite ordinal satisfies $\mathrm{FinOrd}$. Conversely, use membership induction on an ordinal $y$
    satisfying that formula. If $y=\emptyset$, it is finite. Otherwise write $y=z\cup\{z\}$ with $z\in y$.
    Ordinalhood and the zero-or-successor conditions pass to $z$, so the induction hypothesis makes $z$ finite,
    and then $y$ is finite as well.
-/
lemma finiteOrdinal_characterization (x : ZFSet.{u}) :
    (x.IsOrdinal ∧ (x = ∅ ∨ ∃ y ∈ x, x = insert y y) ∧
      ∀ y ∈ x, y = ∅ ∨ ∃ z ∈ y, y = insert z z) ↔ ∃ n, natOrdinal n = x := by
  constructor
  · induction x using ZFSet.inductionOn with
    | h x ih =>
      rintro ⟨ho, h, hall⟩
      rcases h with rfl | ⟨y, hy, he⟩
      · exact ⟨0, natOrdinal_zero⟩
      · obtain ⟨n, hn⟩ := ih y hy ⟨ho.mem hy, hall y hy, fun z hz => hall z (ho.mem_trans hz hy)⟩
        exact ⟨n + 1, by rw [natOrdinal_succ, hn, ← he]⟩
  · rintro ⟨n, rfl⟩
    have hzeroSucc (k : ℕ) : natOrdinal k = (∅ : ZFSet.{u}) ∨
        ∃ y ∈ natOrdinal k, natOrdinal k = insert y y := by
      cases k with
      | zero => exact Or.inl natOrdinal_zero
      | succ k =>
        right
        exact ⟨natOrdinal k, mem_natOrdinal.mpr ⟨k, Nat.lt_succ_self k, rfl⟩, natOrdinal_succ k⟩
    refine ⟨ZFSet.isOrdinal_toZFSet _, hzeroSucc n, ?_⟩
    intro y hy
    obtain ⟨k, _, rfl⟩ := mem_natOrdinal.mp hy
    exact hzeroSucc k

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Bounded absoluteness therefore identifies the internal formula with actual
    membership in $\omega$.
-/
lemma realize_finiteOrdinalFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x : Fin n) (xs : Fin n → ClassDomain C) :
    (finiteOrdinalFormula x).Realize Empty.elim xs ↔ (xs x).val ∈ Ordinal.omega0.toZFSet := by
  simp only [finiteOrdinalFormula, BoundedFormula.realize_inf, realize_ordinalFormula C hC,
    realize_zeroOrSuccessorFormula C hC, realize_boundedAll, Fin.snoc_last]
  rw [mem_omegaOrdinal, ← finiteOrdinal_characterization]
  constructor
  · rintro ⟨⟨ho, h⟩, hall⟩
    exact ⟨ho, h, fun y hy => hall ⟨y, hC _ (xs x).property _ hy⟩ hy⟩
  · rintro ⟨ho, h, hall⟩
    exact ⟨⟨ho, h⟩, fun y hy => hall y.val hy⟩

end PolishSpaceBook.SetTheoryModels
