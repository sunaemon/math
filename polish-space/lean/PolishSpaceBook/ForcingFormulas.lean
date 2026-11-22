module

public import PolishSpaceBook.ForcingAtomicTruth
public import PolishSpaceBook.ForcingLogicalOperations
public import Mathlib.ModelTheory.Encoding
public import Mathlib.ModelTheory.Semantics

@[expose] public section

/-!
# Forcing for the standard first-order language of membership

Mathlib's bounded formulas supply equality, implication and universal
quantification. Membership is the only relation and there are no functions.
The domain of the interpretation is the actual set of evaluated ground names.
-/

noncomputable section
namespace PolishSpaceBook.ForcingFormulas
open FirstOrder Language ZFSet ForcingNames ForcingAtomic
universe u

inductive MembershipSymbol : ℕ → Type
  | mem : MembershipSymbol 2
  deriving DecidableEq

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC is a theory in \termdefine{first-order logic} over the \termdefineas{language of set theory}{language $L_\in$}, and
    this is the \termdefine{logic} used throughout the set-theoretic development. The language has one non-logical symbol,
    the binary relation $\in$; equality $=$ is a logical primitive. It is useful to define first-order syntax for a general
    language first, because later sections use definitional extensions of $L_\in$ and category/realizability sections use
    other first-order languages.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In $L_\in$, the relation-symbol atomic formulas are exactly $t_0 \in t_1$; $\bot$ and equalities $t_0=t_1$ are still
    atomic formulas.
-/
def membershipLanguage : FirstOrder.Language := ⟨fun _ => Empty, MembershipSymbol⟩
  deriving IsRelational

instance (n : ℕ) : Subsingleton (membershipLanguage.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

instance (S : ZFSet.{u}) : membershipLanguage.Structure S where
  RelMap | .mem => fun xs => (xs 0).val ∈ (xs 1).val

abbrev Formula (n : ℕ) := membershipLanguage.BoundedFormula Empty n
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $M^P$ for the class of all $P$-names belonging to $M$.
-/
abbrev Name (P M : ZFSet.{u}) := {σ : ZFSet.{u} // σ ∈ M ∧ IsName P σ}

variable (P M : ZFSet.{u}) [Preorder (Condition P)]

abbrev Extension (G : Order.PFilter (Condition P)) := extension P M (chosen P G)

def evalName (G : Order.PFilter (Condition P)) (σ : Name P M) : Extension P M G :=
  ⟨value P G σ.val, (mem_extension P M (chosen P G) _).mpr ⟨σ.val, σ.property.1, σ.property.2, rfl⟩⟩

lemma evalName_surjective (G : Order.PFilter (Condition P)) : Function.Surjective (evalName P M G) := by
  intro x
  obtain ⟨τ, hτM, hτn, hτ⟩ := (mem_extension P M (chosen P G) x.val).mp x.property
  exact ⟨⟨τ, hτM, hτn⟩, Subtype.ext hτ⟩

def termName {n : ℕ} : membershipLanguage.Term (Empty ⊕ Fin n) → (Fin n → Name P M) → Name P M
  | .var (.inl e), _ => nomatch e
  | .var (.inr i), xs => xs i
  | .func f _, _ => nomatch f

lemma term_realize (G : Order.PFilter (Condition P)) {n : ℕ}
    (t : membershipLanguage.Term (Empty ⊕ Fin n)) (xs : Fin n → Name P M) :
    t.realize (Sum.elim Empty.elim (fun i => evalName P M G (xs i))) = evalName P M G (termName P M t xs) := by
  cases t with
  | var a => cases a with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts => exact f.elim

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \textbf{Connective and quantifier clauses.} Extend $\forces^*$ to all $L_\in$-formulas by recursion on formula
    complexity:
    $$\begin{aligned}
    p \forces^* \varphi \land \psi
    &\Longleftrightarrow p \forces^* \varphi \text{ and } p \forces^* \psi,\\
    p \forces^* \neg\varphi
    &\Longleftrightarrow \text{no } q \le p \text{ satisfies } q \forces^* \varphi,\\
    p \forces^* \varphi \lor \psi
    &\Longleftrightarrow \{q \le p : q \forces^* \varphi \text{ or } q \forces^* \psi\} \text{ is dense below } p,\\
    p \forces^* \varphi \to \psi
    &\Longleftrightarrow \forall q \le p\;(q \forces^* \varphi \Rightarrow q \forces^* \psi),\\
    p \forces^* \exists x\,\varphi(x)
    &\Longleftrightarrow \{q \le p : \exists \tau \in M^P,\; q \forces^* \varphi(\tau)\} \text{ is dense below } p,\\
    p \forces^* \forall x\,\varphi(x)
    &\Longleftrightarrow \forall \tau \in M^P\;\; p \forces^* \varphi(\tau).
    \end{aligned}$$
-/
def force : {n : ℕ} → Formula n → (Fin n → Name P M) → Set (Condition P)
  | _, .falsum, _ => ∅
  | _, .equal s t, xs => atomic P true (termName P M s xs).val (termName P M t xs).val
  | _, .rel .mem ts, xs => atomic P false (termName P M (ts 0) xs).val (termName P M (ts 1) xs).val
  | _, .imp φ ψ, xs => forcingImp (force φ xs) (force ψ xs)
  | _, .all φ, xs => forcingAll (fun τ => force φ (Fin.snoc xs τ))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \item \textbf{Monotonicity.} If $p \forces^* \varphi$ and $q \le p$, then $q \forces^* \varphi$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    the universal-style clauses ($\neg, \to, \forall$) inherit by reusing $q
    \le p$ as a stronger universal hypothesis.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For conjunction, density
    of conditions forcing both conjuncts gives density for each separately, and the induction hypothesis applies.
    For negation, a condition forcing the positive formula would have a refinement forcing its negation, a contradiction.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Two structural properties follow by induction on formula complexity (with the atomic cases checked from the clauses
    above):
-/
lemma force_lower {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) : IsLowerSet (force P M φ xs) := by
  induction φ with
  | falsum => exact fun _ _ _ h => h.elim
  | equal s t => exact atomic_lower P true _ _
  | rel R ts => cases R; exact atomic_lower P false _ _
  | imp φ ψ _ _ => exact forcingImp_lower _ _
  | all φ ih => exact forcingAll_lower _ (fun τ => ih (Fin.snoc xs τ))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \item \textbf{Density-saturation.} If $\{q \le p : q \forces^* \varphi\}$ is dense below $p$, then $p \forces^*
    \varphi$.
-/
lemma force_saturated {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) :
    forcingDense (force P M φ xs) ⊆ force P M φ xs := by
  induction φ with
  | falsum =>
    intro p hp
    obtain ⟨q, _, hq⟩ := hp p le_rfl
    exact hq
  | equal s t => exact fun _ h => atomic_saturated P true _ _ h
  | rel R ts => cases R; exact fun _ h => atomic_saturated P false _ _ h
  | imp φ ψ _ ihψ => exact forcingImp_saturated (force_lower P M φ xs) (ihψ xs)
  | all φ ih => exact forcingAll_saturated (fun τ => ih (Fin.snoc xs τ))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    One may take falsity, the atomic formulas, implication, and universal quantification as primitive.
    No condition forces falsity. The other operations are given by
    $$\begin{aligned}
    \neg\varphi&:=\varphi\to\bot,\\
    \varphi\land\psi&:=\neg(\varphi\to\neg\psi),\\
    \varphi\lor\psi&:=\neg\varphi\to\psi,\\
    \exists x\,\varphi&:=\neg\forall x\,\neg\varphi.
    \end{aligned}$$
    We verify below that these definitions give exactly the displayed forcing clauses, including the density clause
    for the existential quantifier.
-/
lemma force_not {n : ℕ} (φ : Formula n) (xs : Fin n → Name P M) :
    force P M φ.not xs = forcingNeg (force P M φ xs) := rfl

lemma force_and {n : ℕ} (φ ψ : Formula n) (xs : Fin n → Name P M) :
    force P M (φ ⊓ ψ) xs = force P M φ xs ∩ force P M ψ xs := by
  change forcingNeg (forcingImp (force P M φ xs) (forcingNeg (force P M ψ xs))) = _
  exact forcingNeg_forcingImp_neg (force_lower P M φ xs) (force_lower P M ψ xs)
    (force_saturated P M φ xs) (force_saturated P M ψ xs)

lemma force_or {n : ℕ} (φ ψ : Formula n) (xs : Fin n → Name P M) :
    force P M (φ ⊔ ψ) xs = forcingDense (force P M φ xs ∪ force P M ψ xs) := by
  change forcingImp (forcingNeg (force P M φ xs)) (force P M ψ xs) = _
  exact forcingImp_neg_eq_dense_union (force_saturated P M ψ xs)

lemma force_exists {n : ℕ} (φ : Formula (n + 1)) (xs : Fin n → Name P M) :
    force P M φ.ex xs = forcingDense (⋃ τ, force P M φ (Fin.snoc xs τ)) := by
  change forcingNeg (forcingAll (fun τ => forcingNeg (force P M φ (Fin.snoc xs τ)))) = _
  exact forcingNeg_all_neg _

end PolishSpaceBook.ForcingFormulas
