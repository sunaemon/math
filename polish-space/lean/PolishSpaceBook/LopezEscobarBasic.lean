module

public import PolishSpaceBook.InfinitaryLogic
public import PolishSpaceBook.VaughtTransforms
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Finite tuple cosets and the clopen base of Lopez--Escobar

A moving coset fixes the images of a finite tuple. Existentially quantifying
inverse images of a larger target tuple describes its clopen Vaught transforms.
-/

namespace PolishSpaceBook.LopezEscobar

open Set Topology LogicActions InfinitaryLogic
open scoped PointwisePerm

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    We use the relativized Vaught induction. For finite tuples $\bar a$ and $\bar s$ of the same length, put
    $$
    \TupleAgreementCoset{\bar a}{\bar s}
    :=\{\sigma\in\InfiniteSymmetricGroup:\sigma(\bar a)=\bar s\}.
    $$
-/
/-- The finite agreement coset, with the orientation used in the book. -/
def tupleCoset {n} (a s : Fin n → ℕ) : Set (Equiv.Perm ℕ) :=
  {p | ∀ i, p (a i) = s i}

theorem isClopen_tupleCoset {n} (a s : Fin n → ℕ) : IsClopen (tupleCoset a s) := by
  have he : tupleCoset a s = ⋂ i, (fun p : Equiv.Perm ℕ => p (a i)) ⁻¹' {s i} := by
    ext p
    simp [tupleCoset]
  rw [he]
  exact isClopen_iInter_of_finite fun i => (isClopen_discrete _).preimage (PointwisePerm.continuous_apply _)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    If both tuples are injective, this coset is nonempty: the finite bijection $a_i\mapsto s_i$ extends to a permutation
    of $\NN$. The coset is clopen because it imposes finitely many coordinate equalities. The cosets with injective
    source and target tuples form a basis: every neighborhood of a permutation contains a finite-agreement cylinder,
    obtained by enumerating its finite set of specified inputs as $\bar a$ and their images as $\bar s$.
-/
theorem tupleCoset_nonempty {n} {a s : Fin n → ℕ}
    (ha : Function.Injective a) (hs : Function.Injective s) : (tupleCoset a s).Nonempty :=
  Equiv.Perm.exists_extending_pair a s ha hs

/-- Transporting the source tuple corresponds to right translation of the coset. -/
theorem mul_mem_tupleCoset_iff {n} (a s : Fin n → ℕ) (p q : Equiv.Perm ℕ) :
    p * q ∈ tupleCoset a s ↔ p ∈ tupleCoset (q ∘ a) s := Iff.rfl

/-- All nonempty finite-tuple cylinders form a basis for the permutation topology. -/
def tupleCosetBasis : Set (Set (Equiv.Perm ℕ)) :=
  {U | ∃ (n : ℕ) (a s : Fin n → ℕ), Function.Injective a ∧ Function.Injective s ∧ U = tupleCoset a s}

theorem isTopologicalBasis_tupleCosets : TopologicalSpace.IsTopologicalBasis tupleCosetBasis := by
  classical
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨n, a, s, ha, hs, rfl⟩
    exact (isClopen_tupleCoset a s).isOpen
  · intro p U hp hU
    obtain ⟨F, hF⟩ := PointwisePerm.mem_nhds_iff.mp (hU.mem_nhds hp)
    let a : Fin (Fintype.card F) → ℕ := fun i => ((Fintype.equivFin F).symm i).val
    have ha : Function.Injective a := Subtype.val_injective.comp (Fintype.equivFin F).symm.injective
    refine ⟨tupleCoset a (p ∘ a), ⟨_, a, p ∘ a, ha, p.injective.comp ha, rfl⟩, ?_, ?_⟩
    · intro i; rfl
    · intro q hq
      apply hF
      intro x hx
      simpa [a] using hq ((Fintype.equivFin F) ⟨x, hx⟩)

variable {L : FirstOrder.Language}

/-- Finite conjunction, represented using the countable conjunction constructor. -/
def finiteConj {n} (k : ℕ) (φ : Fin k → Formula L n) : Formula L n :=
  .conj fun j => if h : j < k then φ ⟨j, h⟩ else .neg .falsum

theorem realize_finiteConj {M : Type*} [L.Structure M] {n k}
    (φ : Fin k → Formula L n) (a : Fin n → M) :
    (finiteConj k φ).Realize a ↔ ∀ i, (φ i).Realize a := by
  change (∀ j, (if h : j < k then φ ⟨j, h⟩ else Formula.neg Formula.falsum).Realize a) ↔ _
  constructor
  · intro h i
    simpa only [dite_eq_left i.isLt] using h i.val
  · intro h j
    split_ifs with hj
    · exact h ⟨j, hj⟩
    · exact not_false

/-- Eliminate a finite block of variables at the end of the context. -/
def existsBlock {n} : (m : ℕ) → Formula L (n + m) → Formula L n
  | 0, φ => φ
  | m + 1, φ => existsBlock m (.ex φ)

theorem realize_existsBlock {M : Type*} [L.Structure M] {n} (m : ℕ)
    (φ : Formula L (n + m)) (a : Fin n → M) :
    (existsBlock m φ).Realize a ↔ ∃ b : Fin m → M, φ.Realize (Fin.append a b) := by
  induction m with
  | zero =>
    simp only [existsBlock]
    constructor
    · intro h
      exact ⟨Fin.elim0, by simpa using h⟩
    · rintro ⟨b, h⟩
      have hb : b = Fin.elim0 := Subsingleton.elim _ _
      simpa [hb] using h
  | succ m ih =>
    rw [existsBlock, ih]
    change (∃ b : Fin m → M, ∃ c, φ.Realize (Fin.snoc (Fin.append a b) c)) ↔ _
    constructor
    · rintro ⟨b, c, h⟩
      exact ⟨Fin.snoc b c, by simpa only [Fin.append_snoc] using h⟩
    · rintro ⟨b, h⟩
      refine ⟨Fin.init b, b (Fin.last m), ?_⟩
      simpa only [← Fin.append_snoc, Fin.snoc_init_self] using h

/-- Express that the chosen block of variables has no repeated entries. -/
def distinctFormula {n m} (v : Fin m → Fin n) : Formula L n :=
  finiteConj m fun i => finiteConj m fun j =>
    if i = j then .neg .falsum else .neg (.equal (.var (v i)) (.var (v j)))

theorem realize_distinctFormula {M : Type*} [L.Structure M] {n m}
    (v : Fin m → Fin n) (a : Fin n → M) :
    (distinctFormula (L := L) v).Realize a ↔ Function.Injective (a ∘ v) := by
  simp only [distinctFormula, realize_finiteConj]
  constructor
  · intro h i j hij
    by_contra hn
    have hh := h i j
    have hne : a (v i) ≠ a (v j) := by
      simpa only [ite_eq_right hn, Formula.Realize, FirstOrder.Language.Term.realize] using hh
    exact hne hij
  · intro h i j
    split_ifs with hij
    · exact not_false
    · exact fun he => hij (h he)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{mathmeta}
      \define{InverseTupleFormula}
    \end{mathmeta}
    Define the formula
    $$
    \begin{aligned}
    \InverseTupleFormula{e}{\psi}(\bar x):={}&\exists y_0\cdots\exists y_{m-1}\\
    &\Bigl[\bigwedge_{j<k<m}y_j\ne y_k\\
    &\qquad\land\bigwedge_{i<n}y_{e(i)}=x_i\land\psi(\bar y)\Bigr].
    \end{aligned}
    $$
    The bound variables are chosen fresh. The free variables of this formula are among $x_0,\ldots,x_{n-1}$.
    Finite conjunction and the displayed finite block of quantifiers are built from the constructors above.
-/
/-- Existential inverse images of a target tuple, constrained by the original free tuple. -/
def extensionFormula {n m} (e : Fin n → Fin m) (φ : Formula L m) : Formula L n :=
  existsBlock m (finiteConj 3 fun i =>
    if i.val = 0 then distinctFormula (Fin.natAdd n) else
    if i.val = 1 then finiteConj n fun j =>
      .equal (.var (Fin.natAdd n (e j))) (.var (Fin.castAdd m j))
    else φ.rename (Fin.natAdd n))

theorem realize_extensionFormula {M : Type*} [L.Structure M] {n m}
    (e : Fin n → Fin m) (φ : Formula L m) (a : Fin n → M) :
    (extensionFormula e φ).Realize a ↔
      ∃ b : Fin m → M, Function.Injective b ∧ b ∘ e = a ∧ φ.Realize b := by
  simp only [extensionFormula, realize_existsBlock, realize_finiteConj]
  apply exists_congr
  intro b
  have hb : Fin.append a b ∘ Fin.natAdd n = b := by funext j; simp
  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ]
  simp [realize_finiteConj, realize_distinctFormula, Formula.realize_rename, Formula.Realize,
    FirstOrder.Language.Term.realize, hb, funext_iff, Function.comp_def]

/-- Isomorphism invariance with the assignment transported along relabeling. -/
theorem satisfies_smul_iff {n} (φ : Formula L n) (M : ModelCode L)
    (p : Equiv.Perm ℕ) (a : Fin n → ℕ) :
    φ.Satisfies (p • M) (p ∘ a) ↔ φ.Satisfies M a :=
  φ.realize_equiv (relabelIso L p M) a

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For any formula $\psi$ in the context of $\bar t$, the meaning of this construction is
    $$
    \begin{aligned}
    &M\models\InverseTupleFormula{e}{\psi}(\bar a)\\
    &\quad\Longleftrightarrow\quad
    \exists\sigma\in\TupleAgreementCoset{\bar a}{\bar s}\;
    \sigma\cdot M\models\psi(\bar t).
    \end{aligned}
    $$
    Indeed, given such a $\sigma$, put $b_j=\sigma^{-1}(t_j)$. The $b_j$ are distinct and satisfy $b_{e(i)}=a_i$;
    isomorphism invariance with the assignment transported by $\sigma$ gives $M\models\psi(\bar b)$.
    Conversely, a tuple $\bar b$ satisfying the formula defines a finite bijection $b_j\mapsto t_j$.
    Extend it to a permutation $\sigma$. Then $\sigma(\bar a)=\bar s$ and the same invariance gives
    $\sigma\cdot M\models\psi(\bar t)$.
-/
/-- Finite inverse-image witnesses extend to a permutation, and conversely. -/
theorem exists_coset_satisfies_iff {n m} (e : Fin n → Fin m) (t : Fin m → ℕ)
    (ht : Function.Injective t) (φ : Formula L m) (M : ModelCode L) (a : Fin n → ℕ) :
    (∃ p ∈ tupleCoset a (t ∘ e), φ.Satisfies (p • M) t) ↔
      (extensionFormula e φ).Satisfies M a := by
  rw [Formula.Satisfies, realize_extensionFormula]
  constructor
  · rintro ⟨p, hp, hφ⟩
    let b := p.symm ∘ t
    have hb : p ∘ b = t := by funext i; simp [b]
    refine ⟨b, p.symm.injective.comp ht, ?_, ?_⟩
    · funext i
      exact p.symm_apply_eq.mpr (hp i).symm
    · exact (satisfies_smul_iff φ M p b).mp (by rwa [hb])
  · rintro ⟨b, hb, he, hφ⟩
    obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair b t hb ht
    refine ⟨p, ?_, ?_⟩
    · intro i
      rw [← congrFun he i]
      exact hp (e i)
    · have ht' : p ∘ b = t := funext hp
      rw [← ht']
      exact (satisfies_smul_iff φ M p b).mpr hφ

/-- For an open satisfaction set, the existential extension formula is its nonmeager transform. -/
theorem satisfies_extensionFormula_iff_star {n m} (e : Fin n → Fin m) (t : Fin m → ℕ)
    (ht : Function.Injective t) (φ : Formula L m)
    (hφ : IsOpen {M : ModelCode L | φ.Satisfies M t}) (M : ModelCode L) (a : Fin n → ℕ) :
    (extensionFormula e φ).Satisfies M a ↔
      M ∈ vaughtStar (tupleCoset a (t ∘ e)) {N : ModelCode L | φ.Satisfies N t} := by
  rw [vaughtStar_open_eq (isClopen_tupleCoset a (t ∘ e)).isOpen hφ]
  exact (exists_coset_satisfies_iff e t ht φ M a).symm

/-- Duality gives the comeager transform of a closed satisfaction set. -/
theorem satisfies_neg_extensionFormula_iff_triangle {n m} (e : Fin n → Fin m) (t : Fin m → ℕ)
    (ht : Function.Injective t) (φ : Formula L m)
    (hφ : IsClosed {M : ModelCode L | φ.Satisfies M t}) (M : ModelCode L) (a : Fin n → ℕ) :
    (Formula.neg (extensionFormula e φ.neg)).Satisfies M a ↔
      M ∈ vaughtTriangle (tupleCoset a (t ∘ e)) {N : ModelCode L | φ.Satisfies N t} := by
  have hd := vaughtStar_compl (tupleCoset a (t ∘ e)) {N : ModelCode L | φ.neg.Satisfies N t}
  have he : {N : ModelCode L | φ.neg.Satisfies N t}ᶜ = {N | φ.Satisfies N t} := by
    ext N
    simp [Formula.Satisfies, Formula.Realize]
  rw [he] at hd
  rw [← hd]
  exact not_congr (satisfies_extensionFormula_iff_star e t ht φ.neg hφ.isOpen_compl M a)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For the basic clopen case, let $B$ be given by finitely many relation-bit and function-value conditions.
    Choose a tuple $\bar t=(t_0,\ldots,t_{m-1})$ listing, without repetition, all the entries of $\bar s$ and all the
    natural numbers named in these conditions, including function outputs. Write $s_i=t_{e(i)}$ for $i<n$.
    Replacing each named value $t_j$ by $y_j$ gives a finite conjunction $\psi(\bar y)$ of atomic or negated atomic
    formulas such that
    $$M\in B\quad\Longleftrightarrow\quad M\models\psi(\bar t).$$
    A relation bit gives $R(y_{j_1},\ldots,y_{j_k})$ or its negation; a function value gives
    $f(y_{j_1},\ldots,y_{j_k})=y_\ell$. Nullary symbols and the empty conjunction are allowed.
-/
/-- A single relation-bit or function-value coordinate condition. -/
inductive CoordinateAtom (L : FirstOrder.Language) (m : ℕ)
  | rel {k} (r : L.Relations k) (args : Fin k → Fin m) (value : Bool)
  | func {k} (f : L.Functions k) (args : Fin k → Fin m) (out : Fin m)

/-- Read a coordinate condition at the tuple of named elements. -/
def CoordinateAtom.Holds {m} : CoordinateAtom L m → ModelCode L → (Fin m → ℕ) → Prop
  | .rel r args value, M, t => M.1 ⟨⟨_, r⟩, t ∘ args⟩ = value
  | .func f args out, M, t => M.2 ⟨⟨_, f⟩, t ∘ args⟩ = t out

/-- Replace names by variables in each table condition. -/
def CoordinateAtom.formula {m} : CoordinateAtom L m → Formula L m
  | .rel r args true => .rel r (fun i => .var (args i))
  | .rel r args false => .neg (.rel r (fun i => .var (args i)))
  | .func f args out => .equal (.func f (fun i => .var (args i))) (.var out)

theorem CoordinateAtom.satisfies_formula {m} (c : CoordinateAtom L m)
    (M : ModelCode L) (t : Fin m → ℕ) : c.formula.Satisfies M t ↔ c.Holds M t := by
  cases c with
  | rel r args value =>
    cases value
    · change (¬ M.1 ⟨⟨_, r⟩, t ∘ args⟩ = true) ↔ M.1 ⟨⟨_, r⟩, t ∘ args⟩ = false
      simp
    · rfl
  | func f args out => rfl

theorem CoordinateAtom.isClopen_holds {m} (c : CoordinateAtom L m) (t : Fin m → ℕ) :
    IsClopen {M : ModelCode L | c.Holds M t} := by
  cases c with
  | rel r args value =>
    exact (isClopen_discrete {value}).preimage
      ((_root_.continuous_apply (⟨⟨_, r⟩, t ∘ args⟩ : RelIndex L)).comp continuous_fst)
  | func f args out =>
    exact (isClopen_discrete {t out}).preimage
      ((_root_.continuous_apply (⟨⟨_, f⟩, t ∘ args⟩ : FunIndex L)).comp continuous_snd)

/-- A finite table diagram, including the empty diagram and nullary symbols. -/
abbrev Diagram (L : FirstOrder.Language) (m : ℕ) := List (CoordinateAtom L m)

def Diagram.formula {m} (d : Diagram L m) : Formula L m :=
  finiteConj d.length fun i => (d.get i).formula

def Diagram.set {m} (d : Diagram L m) (t : Fin m → ℕ) : Set (ModelCode L) :=
  {M | ∀ i, (d.get i).Holds M t}

theorem Diagram.satisfies_formula {m} (d : Diagram L m) (M : ModelCode L) (t : Fin m → ℕ) :
    d.formula.Satisfies M t ↔ M ∈ d.set t := by
  change (finiteConj d.length fun i => (d.get i).formula).Realize (M := ModelCarrier L M) t ↔ _
  rw [realize_finiteConj]
  exact forall_congr' fun i => (d.get i).satisfies_formula M t

theorem Diagram.isClopen_set {m} (d : Diagram L m) (t : Fin m → ℕ) : IsClopen (d.set t) := by
  change IsClopen {M : ModelCode L | ∀ i, (d.get i).Holds M t}
  simp only [Set.ofPred_forall]
  exact isClopen_iInter_of_finite fun i => (d.get i).isClopen_holds t

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For the finite diagram defining $B$, the action section is clopen in $\TupleAgreementCoset{\bar a}{\bar s}$.
    A nonempty open subset of this Baire space is non-meager, so its non-meager transform is given by
    $\InverseTupleFormula{e}{\psi}$. Applying the same argument to the complementary clopen condition and using duality
    therefore gives the two formulas
    $$
    \begin{aligned}
    \varphi^{\bar s}_{B,*}(\bar x)&:=\InverseTupleFormula{e}{\psi}(\bar x),\\
    \varphi^{\bar s}_{B,\triangle}(\bar x)&:=\neg\InverseTupleFormula{e}{\neg\psi}(\bar x).
    \end{aligned}
    $$
    In particular, the base case gives actual formulas with only the original finite tuple of free variables.
-/
/-- The explicit formula for the nonmeager transform of a finite coordinate diagram. -/
theorem Diagram.extensionFormula_iff_star {n m} (d : Diagram L m) (e : Fin n → Fin m)
    (t : Fin m → ℕ) (ht : Function.Injective t) (M : ModelCode L) (a : Fin n → ℕ) :
    (extensionFormula e d.formula).Satisfies M a ↔
      M ∈ vaughtStar (tupleCoset a (t ∘ e)) (d.set t) := by
  have he : {N : ModelCode L | d.formula.Satisfies N t} = d.set t :=
    Set.ext fun N => d.satisfies_formula N t
  have ho : IsOpen {N : ModelCode L | d.formula.Satisfies N t} := by
    rw [he]; exact (d.isClopen_set t).isOpen
  simpa only [he] using satisfies_extensionFormula_iff_star e t ht d.formula ho M a

/-- Negating the existential formula for the complementary diagram condition gives comeagerness. -/
theorem Diagram.neg_extensionFormula_iff_triangle {n m} (d : Diagram L m) (e : Fin n → Fin m)
    (t : Fin m → ℕ) (ht : Function.Injective t) (M : ModelCode L) (a : Fin n → ℕ) :
    (Formula.neg (extensionFormula e d.formula.neg)).Satisfies M a ↔
      M ∈ vaughtTriangle (tupleCoset a (t ∘ e)) (d.set t) := by
  have he : {N : ModelCode L | d.formula.Satisfies N t} = d.set t :=
    Set.ext fun N => d.satisfies_formula N t
  have hc : IsClosed {N : ModelCode L | d.formula.Satisfies N t} := by
    rw [he]; exact (d.isClopen_set t).isClosed
  simpa only [he] using satisfies_neg_extensionFormula_iff_triangle e t ht d.formula hc M a

end PolishSpaceBook.LopezEscobar
