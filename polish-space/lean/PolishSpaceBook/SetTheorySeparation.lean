module

public import PolishSpaceBook.SetTheoryModelSchemes

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Deriving Separation by replacing elements with singletons or the empty set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- The graph of the operation sending a to {a} if φ(a), and to ∅ otherwise. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Choose fresh variables $b,z$ and put
    $$\theta(a,b,\vec p)\;:\equiv\;
    \forall z\,(z\in b\leftrightarrow z=a\land\varphi(a,\vec p)).$$
    If $\varphi(a,\vec p)$ holds, Pairing supplies $b=\{a\}$; otherwise the empty set supplied by Infinity is suitable.
    In either case, Extensionality makes $b$ unique. This establishes the premise of Replacement without using
    Separation.
-/
def singletonSelector {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula (n + 2) :=
  ((memberAt (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
    (equalAt (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc ⊓
      reindex φ (Fin.snoc (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc))).all

namespace AbstractMembership

lemma realize_singletonSelector (S : Type u) [membershipLanguage.Structure S] {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (v : Empty → S) (ps : Fin n → S) (a b : S) :
    (singletonSelector φ).Realize v (Fin.snoc (Fin.snoc ps a) b) ↔
      ∀ z : S, member z b ↔ z = a ∧ φ.Realize v (Fin.snoc ps a) := by
  simp only [singletonSelector, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memberAt, realize_equalAt, realize_reindex,
    apply_snoc, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]

end AbstractMembership

lemma realize_singletonSelector (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (v : Empty → S) (ps : Fin n → S) (a b : S) :
    (singletonSelector φ).Realize v (Fin.snoc (Fin.snoc ps a) b) ↔
      ∀ z : S, z.val ∈ b.val ↔ z = a ∧ φ.Realize v (Fin.snoc ps a) :=
  AbstractMembership.realize_singletonSelector S φ v ps a b

namespace AbstractMembership

/-- A single Replacement instance suffices for each Separation instance.
The proof is internal and does not assume that the domain is transitive. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Apply Replacement to $\theta$ on the given set $x$ to obtain a set $C$ satisfying
    $$b\in C\quad\Longleftrightarrow\quad\exists a\in x\,\theta(a,b,\vec p).$$
    Union now gives $\bigcup C$, and
    $$\begin{aligned}
    z\in\bigcup C
    &\Longleftrightarrow\exists a\in x\,(z=a\land\varphi(a,\vec p))\\
    &\Longleftrightarrow z\in x\land\varphi(z,\vec p).
    \end{aligned}$$
    Thus $\bigcup C$ is the required subset. Each step uses only the model's own quantifiers and axioms, so
    no appeal to external elements or transitivity enters the derivation.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: lemma
  title: Deriving Separation
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix an arbitrary $L_\in$-structure satisfying the hypotheses. Throughout this proof, $\in$ denotes
    its interpreted membership relation, and all variables and quantifiers range over its domain.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In the presence of Replacement, however, Separation is
    redundant: after $\emptyset$ has been derived from Infinity, replace each $a \in x$ by $\{a\}$ if $\varphi(a,\vec p)$
    holds and by $\emptyset$ otherwise, then take the union of the resulting set.
-/
theorem models_separation_of_replacement (S : Type u) [membershipLanguage.Structure S]
    (hext : S ⊨ extensionalitySentence) (hinf : S ⊨ infinitySentence)
    (hpair : S ⊨ pairingSentence) (hunion : S ⊨ unionSentence)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hrep : S ⊨ replacementSentence (singletonSelector φ)) : S ⊨ separationSentence φ := by
  classical
  apply (realize_separation S φ).mpr
  intro ps x
  obtain ⟨e, he⟩ := (models_empty_iff S).mp (models_empty_of_infinity hinf)
  have hf (a : S) : ∃! b : S,
      (singletonSelector φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
    have hex : ∃ b : S, ∀ z : S,
        member z b ↔ z = a ∧ φ.Realize Empty.elim (Fin.snoc ps a) := by
      by_cases hφ : φ.Realize Empty.elim (Fin.snoc ps a)
      · obtain ⟨b, hb⟩ := (models_pairing_iff S).mp hpair a a
        refine ⟨b, ?_⟩
        intro z
        simpa only [hφ, and_true, or_self] using hb z
      · refine ⟨e, ?_⟩
        intro z
        constructor
        · intro hz
          exact False.elim (he z hz)
        · rintro ⟨_, hz⟩
          exact False.elim (hφ hz)
    obtain ⟨b, hb⟩ := hex
    refine ⟨b, (realize_singletonSelector S φ Empty.elim ps a b).mpr hb, ?_⟩
    intro c hc
    apply (models_extensionality_iff S).mp hext c b
    intro z
    rw [hb z, (realize_singletonSelector S φ Empty.elim ps a c).mp hc z]
  obtain ⟨y, hy⟩ := (realize_replacement S (singletonSelector φ)).mp hrep ps x (fun a _ => hf a)
  obtain ⟨u, hu⟩ := (models_union_iff S).mp hunion y
  refine ⟨u, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨b, hzb, hby⟩ := (hu z).mp hz
    obtain ⟨a, hax, hab⟩ := (hy b).mp hby
    obtain ⟨hza, hφ⟩ := (realize_singletonSelector S φ Empty.elim ps a b).mp hab z |>.mp hzb
    subst z
    exact ⟨hax, hφ⟩
  · rintro ⟨hzx, hφ⟩
    obtain ⟨b, hb, _⟩ := hf z
    apply (hu z).mpr
    refine ⟨b, ?_, (hy b).mpr ⟨z, hzx, hb⟩⟩
    exact ((realize_singletonSelector S φ Empty.elim ps z b).mp hb z).mpr ⟨rfl, hφ⟩

end AbstractMembership

theorem models_separation_of_replacement (S : ZFSet.{u})
    (hext : S ⊨ extensionalitySentence) (hinf : S ⊨ infinitySentence)
    (hpair : S ⊨ pairingSentence) (hunion : S ⊨ unionSentence)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hrep : S ⊨ replacementSentence (singletonSelector φ)) : S ⊨ separationSentence φ :=
  AbstractMembership.models_separation_of_replacement S hext hinf hpair hunion φ hrep

/-- With an absolute predicate, the internal subset is exactly the external separation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For Separation, take its internal witness $y\in M$. Every actual element of $y$ or $x$ lies in $M$ by
    transitivity. Hence the internal characterization of $y$, together with the assumed equivalence, gives
    $$a\in y\quad\Longleftrightarrow\quad a\in x\land R(a)$$
    for all actual sets $a$. Thus $y=\{a\in x:R(a)\}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Separation and definable images in a transitive model
-/
theorem separation_mem_of_absolute {S : ZFSet.{u}} (hS : S.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) (hsep : S ⊨ separationSentence φ)
    (ps : Fin n → S) {x : ZFSet.{u}} (hx : x ∈ S) (R : ZFSet.{u} → Prop)
    (hR : ∀ z : S, z.val ∈ x → (φ.Realize Empty.elim (Fin.snoc ps z) ↔ R z.val)) :
    x.sep R ∈ S := by
  obtain ⟨y, hy⟩ := (realize_separation S φ).mp hsep ps ⟨x, hx⟩
  have heq : y.val = x.sep R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · intro hz
      let zS : S := ⟨z, hS.mem_trans hz y.property⟩
      obtain ⟨hzx, hφ⟩ := (hy zS).mp hz
      exact ⟨hzx, (hR zS hzx).mp hφ⟩
    · rintro ⟨hzx, hzR⟩
      let zS : S := ⟨z, hS.mem_trans hzx hx⟩
      exact (hy zS).mpr ⟨hzx, (hR zS hzx).mpr hzR⟩
  exact heq ▸ y.property

/-- Interpret a formula in the ambient class of all sets of the chosen universe. -/
def externalRealize {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → ZFSet.{u}) : Prop :=
  φ.Realize (M := ClassDomain (⊤ : ZFClass.{u})) Empty.elim (fun i => ⟨xs i, trivial⟩)

lemma delta_zero_external {S : ZFSet.{u}} (hS : S.IsTransitive)
    {n : ℕ} {φ : ForcingFormulas.Formula n} (hφ : IsDeltaZero φ) (xs : Fin n → S) :
    φ.Realize Empty.elim xs ↔ externalRealize φ (fun i => (xs i).val) :=
  delta_zero_absolute (S : ZFClass.{u}) ⊤ (fun _ _ => trivial)
    (fun _ ha _ hb => hS.mem_trans hb ha) hφ xs

/-- Delta-zero Separation selects the same subset internally and externally. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Separation and definable images in a transitive model
-/
theorem delta_zero_separation_mem {S : ZFSet.{u}} (hS : S.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) (hφ : IsDeltaZero φ)
    (hsep : S ⊨ separationSentence φ) (ps : Fin n → S) {x : ZFSet.{u}} (hx : x ∈ S) :
    x.sep (fun z => externalRealize φ (Fin.snoc (fun i => (ps i).val) z)) ∈ S := by
  apply separation_mem_of_absolute hS φ hsep ps hx
  intro z _
  simpa only [apply_snoc] using delta_zero_external hS hφ (Fin.snoc ps z)

/-- Bounded external separation follows from the indicated elementary axioms and Replacement. -/
theorem delta_zero_separation_mem_of_replacement {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hinf : S ⊨ infinitySentence) (hpair : S ⊨ pairingSentence) (hunion : S ⊨ unionSentence)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) (hφ : IsDeltaZero φ)
    (hrep : S ⊨ replacementSentence (singletonSelector φ))
    (ps : Fin n → S) {x : ZFSet.{u}} (hx : x ∈ S) :
    x.sep (fun z => externalRealize φ (Fin.snoc (fun i => (ps i).val) z)) ∈ S :=
  delta_zero_separation_mem hS φ hφ
    (models_separation_of_replacement S (models_extensionality hS) hinf hpair hunion φ hrep) ps hx

/-- An internally definable function into the model has its set-sized image in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For the image, the graph condition and $f(a)\in M$ give exactly one internal output for each $a\in x$.
    Replacement supplies $Y\in M$ such that, for $b\in M$, membership $b\in Y$ is equivalent to
    $\psi(a,b,\vec p)$ holding internally for some $a\in x$.
    Every member of $Y$ lies in $M$, so the graph condition identifies it with a value $f(a)$.
    Conversely, each value $f(a)$ lies in $M$ and satisfies that condition, so it belongs to $Y$.
    Thus $Y=f[x]$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Separation and definable images in a transitive model
-/
theorem replacement_image_mem {S : ZFSet.{u}} (hS : S.IsTransitive)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) (hrep : S ⊨ replacementSentence φ)
    (ps : Fin n → S) {x : ZFSet.{u}} (hx : x ∈ S) (f : x → S)
    (hf : ∀ a : x, ∀ b : S,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps ⟨a.val, hS.mem_trans a.property hx⟩) b) ↔ b = f a) :
    ZFSet.range (fun a : x => (f a).val) ∈ S := by
  have ht (a : S) (ha : a.val ∈ x) :
      ∃! b : S, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
    have hg := hf ⟨a.val, ha⟩
    change ∀ b : S, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔ b = f ⟨a.val, ha⟩ at hg
    refine ⟨f ⟨a.val, ha⟩, (hg _).mpr rfl, ?_⟩
    intro b hb
    exact (hg b).mp hb
  obtain ⟨y, hy⟩ := (realize_replacement S φ).mp hrep ps ⟨x, hx⟩ ht
  have heq : y.val = ZFSet.range (fun a : x => (f a).val) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    constructor
    · intro hz
      let zS : S := ⟨z, hS.mem_trans hz y.property⟩
      obtain ⟨a, ha, hab⟩ := (hy zS).mp hz
      have h := (hf ⟨a.val, ha⟩ zS).mp hab
      exact ⟨⟨a.val, ha⟩, (congrArg Subtype.val h).symm⟩
    · rintro ⟨a, rfl⟩
      apply (hy (f a)).mpr
      exact ⟨⟨a.val, hS.mem_trans a.property hx⟩, a.property, (hf a (f a)).mpr rfl⟩
  exact heq ▸ y.property

end PolishSpaceBook.SetTheoryModels
