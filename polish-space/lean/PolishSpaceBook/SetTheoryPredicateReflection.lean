module

public import PolishSpaceBook.SetTheoryFiniteSequences
public import PolishSpaceBook.SetTheoryInternalOrderMinima

@[expose] public section

/-! # Verified compilation of bounded set predicates

This is syntax for first-order predicates, not a computation model. Atomic
abbreviations use their existing membership-language definitions. The single
compiler theorem transfers their Boolean combinations and bounded quantifiers
to transitive models, avoiding a new absoluteness proof for every finite test.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma forall_mem_omegaOrdinal (P : ZFSet.{u} → Prop) :
    (∀ x ∈ Ordinal.omega0.toZFSet, P x) ↔ ∀ n : ℕ, P (natOrdinal n) := by
  constructor
  · intro h n
    exact h _ (mem_omegaOrdinal.mpr ⟨n, rfl⟩)
  · intro h x hx
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx
    exact h n

lemma exists_mem_omegaOrdinal (P : ZFSet.{u} → Prop) :
    (∃ x ∈ Ordinal.omega0.toZFSet, P x) ↔ ∃ n : ℕ, P (natOrdinal n) := by
  exact ⟨fun ⟨x, hx, hp⟩ => by obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx; exact ⟨n, hp⟩,
    fun ⟨n, hp⟩ => ⟨natOrdinal n, mem_omegaOrdinal.mpr ⟨n, rfl⟩, hp⟩⟩

inductive BoundedSetPredicate : ℕ → Type
  | equal {n} (i j : Fin n) : BoundedSetPredicate n
  | member {n} (i j : Fin n) : BoundedSetPredicate n
  | orderedPair {n} (p i j : Fin n) : BoundedSetPredicate n
  | pairMember {n} (r i j : Fin n) : BoundedSetPredicate n
  | function {n} (a b g : Fin n) : BoundedSetPredicate n
  | successor {n} (a b : Fin n) : BoundedSetPredicate n
  | subset {n} (a b : Fin n) : BoundedSetPredicate n
  | neg {n} (p : BoundedSetPredicate n) : BoundedSetPredicate n
  | conj {n} (p q : BoundedSetPredicate n) : BoundedSetPredicate n
  | disj {n} (p q : BoundedSetPredicate n) : BoundedSetPredicate n
  | iff {n} (p q : BoundedSetPredicate n) : BoundedSetPredicate n
  | all {n} (a : Fin n) (p : BoundedSetPredicate (n + 1)) : BoundedSetPredicate n
  | ex {n} (a : Fin n) (p : BoundedSetPredicate (n + 1)) : BoundedSetPredicate n

namespace BoundedSetPredicate

def eval : {n : ℕ} → BoundedSetPredicate n → (Fin n → ZFSet.{u}) → Prop
  | _, .equal i j, xs => xs i = xs j
  | _, .member i j, xs => xs i ∈ xs j
  | _, .orderedPair p i j, xs => xs p = pair (xs i) (xs j)
  | _, .pairMember r i j, xs => pair (xs i) (xs j) ∈ xs r
  | _, .function a b g, xs => IsFunc (xs a) (xs b) (xs g)
  | _, .successor a b, xs => xs a = insert (xs b) (xs b)
  | _, .subset a b, xs => xs a ⊆ xs b
  | _, .neg p, xs => ¬p.eval xs
  | _, .conj p q, xs => p.eval xs ∧ q.eval xs
  | _, .disj p q, xs => p.eval xs ∨ q.eval xs
  | _, .iff p q, xs => p.eval xs ↔ q.eval xs
  | _, .all a p, xs => ∀ x ∈ xs a, p.eval (Fin.snoc xs x)
  | _, .ex a p, xs => ∃ x ∈ xs a, p.eval (Fin.snoc xs x)

def compile : {n : ℕ} → BoundedSetPredicate n → ForcingFormulas.Formula n
  | _, .equal i j => equalAt i j
  | _, .member i j => memberAt i j
  | _, .orderedPair p i j => orderedPairFormula p i j
  | _, .pairMember r i j => pairMemberFormula r i j
  | _, .function a b g => functionFormula a b g
  | _, .successor a b => successorFormula a b
  | _, .subset a b => orderSubsetFormula a b
  | _, .neg p => p.compile.not
  | _, .conj p q => p.compile ⊓ q.compile
  | _, .disj p q => p.compile ⊔ q.compile
  | _, .iff p q => p.compile.iff q.compile
  | _, .all a p => boundedAll a p.compile
  | _, .ex a p => boundedExists a p.compile

/-- Compiled descriptions remain in the bounded fragment of the membership language. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Complexity claims are stricter: whenever
    §{sec:zfc-absoluteness} calls a formula $\Delta_0$, $\Sigma_n$, or $\Pi_n$, the claim is about its unfolded $L_\in$
    form. The definitions below are chosen so the routine atomic uses needed there unfold with only bounded
    quantifiers.\termref{absoluteness}
-/
theorem compile_deltaZero {n : ℕ} (p : BoundedSetPredicate n) : IsDeltaZero p.compile := by
  induction p with
  | equal i j => exact equalAt_deltaZero i j
  | member i j => exact .member _
  | orderedPair p i j => exact orderedPairFormula_deltaZero p i j
  | pairMember r i j => exact pairMemberFormula_deltaZero r i j
  | function a b g => exact functionFormula_deltaZero a b g
  | successor a b => exact successorFormula_deltaZero a b
  | subset a b => exact .all a (.member _)
  | neg p ih => exact ih.not
  | conj p q ihp ihq => exact ihp.and ihq
  | disj p q ihp ihq => exact ihp.or ihq
  | iff p q ihp ihq => exact (ihp.imp ihq).and (ihq.imp ihp)
  | all a p ih => exact .all a ih
  | ex a p ih => exact .exists a ih

/-- Correctness for every finite predicate description, proved once by structural induction. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    All predicates below use equality, membership, ordered-pair membership, function-graph conditions, successor,
    and inclusion, combined by Boolean connectives and bounded quantifiers. After the bounded expansions of
    §{sec:zfc-absoluteness}, each resulting formula $\varphi$ is $\Delta_0$. For parameters $\vec\eta$ in a transitive
    set $M$, the absoluteness theorem in that section gives, uniformly,
    $$M\models\varphi(\vec\eta)\quad\Longleftrightarrow\quad\varphi(\vec\eta).$$
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The uniform interpretation principle gives all the internal equivalences at once.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    These arguments prove
    the external equivalences.
-/
theorem realize_compile {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (p : BoundedSetPredicate n) (xs : Fin n → M) :
    p.compile.Realize Empty.elim xs ↔ p.eval (Subtype.val ∘ xs) := by
  induction p with
  | equal i j => exact (realize_equalAt_model M i j xs).trans Subtype.ext_iff
  | member i j => exact realize_memberAt_model M i j xs
  | orderedPair p i j =>
    exact realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) p i j xs
  | pairMember r i j => exact realize_pairMemberFormula_model hM r i j xs
  | function a b g =>
    exact realize_functionFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) a b g xs
  | successor a b =>
    exact realize_successorFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) a b xs
  | subset a b => exact realize_orderSubsetFormula hM a b xs
  | neg p ih => exact not_congr (ih xs)
  | conj p q ihp ihq =>
    simpa only [compile, eval, BoundedFormula.realize_inf] using and_congr (ihp xs) (ihq xs)
  | disj p q ihp ihq =>
    simpa only [compile, eval, BoundedFormula.realize_sup] using or_congr (ihp xs) (ihq xs)
  | iff p q ihp ihq =>
    simpa only [compile, eval, BoundedFormula.realize_iff] using iff_congr (ihp xs) (ihq xs)
  | all a p ih =>
    have hAll : (boundedAll a p.compile).Realize Empty.elim xs ↔
        ∀ x : M, x.val ∈ (xs a).val → p.compile.Realize Empty.elim (Fin.snoc xs x) :=
      realize_boundedAll (M : ZFClass) a p.compile xs
    rw [compile, hAll]
    constructor
    · intro h x hx
      let y : M := ⟨x, hM.mem_trans hx (xs a).property⟩
      have ht := (ih (Fin.snoc xs y)).mp (h y hx)
      simpa only [Fin.comp_snoc] using ht
    · intro h x hx
      apply (ih (Fin.snoc xs x)).mpr
      simpa only [Fin.comp_snoc] using h x.val hx
  | ex a p ih =>
    rw [compile, realize_boundedExists_model]
    constructor
    · rintro ⟨x, hx, hp⟩
      refine ⟨x.val, hx, ?_⟩
      simpa only [Fin.comp_snoc] using (ih (Fin.snoc xs x)).mp hp
    · rintro ⟨x, hx, hp⟩
      let y : M := ⟨x, hM.mem_trans hx (xs a).property⟩
      refine ⟨y, hx, (ih (Fin.snoc xs y)).mpr ?_⟩
      simpa only [Fin.comp_snoc] using hp

/-- A described predicate gives an internal subset without a fresh absoluteness argument. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Consequently, if $A\in M$ and the corresponding Separation instance holds, then
    $$\{x\in A:\varphi(\vec\eta,x)\}\in M.$$
    We use this consequence throughout the construction. It remains to check the ordinary mathematical meaning of
    each finite-word predicate; its internal interpretation and the collection of its values then follow from the
    same two principles.
-/
theorem separation_mem {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (p : BoundedSetPredicate (n + 1)) (hsep : M ⊨ separationSentence p.compile)
    (ps : Fin n → M) {A : ZFSet.{u}} (hA : A ∈ M) :
    A.sep (fun x => p.eval (Fin.snoc (Subtype.val ∘ ps) x)) ∈ M := by
  apply separation_mem_of_absolute hM p.compile hsep ps hA
  intro x _
  simpa only [Fin.comp_snoc] using p.realize_compile hM (Fin.snoc ps x)

/-- Recognizing membership on an internal bound suffices; no internality of `B` is assumed. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal subsets from bounded recognition
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Absoluteness identifies the internal and external interpretations of $\varphi$ on $A$.
    Separation therefore gives $\{x\in A:\varphi(\vec\eta,x)\}\in M$. The recognition equivalence and
    $B\IncludedIn A$ identify this set with $B$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This lemma applies equally to graphs of functions and sets of tree nodes. In each application, specify an
    internal ambient set, verify that every parameter belongs to $M$, and prove the recognition equivalence
    there. The internal interpretation and the collection step then follow from the lemma. For numerical
    pairing and its inverse projections in §{sec:internal-natural-arithmetic}, the parameters are $\omega$ and
    the previously constructed arithmetic graphs. No separate correspondence between internal and external
    natural-number witnesses is needed for each operation.
-/
theorem subset_mem {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (p : BoundedSetPredicate (n + 1)) (hsep : M ⊨ separationSentence p.compile)
    (ps : Fin n → M) {A B : ZFSet.{u}} (hA : A ∈ M) (hBA : B ⊆ A)
    (heval : ∀ x ∈ A, p.eval (Fin.snoc (Subtype.val ∘ ps) x) ↔ x ∈ B) : B ∈ M := by
  have h := p.separation_mem hM hsep ps hA
  have he : A.sep (fun x => p.eval (Fin.snoc (Subtype.val ∘ ps) x)) = B := by
    ext x
    rw [ZFSet.mem_sep]
    exact ⟨fun hx => (heval x hx.1).mp hx.2,
      fun hx => ⟨hBA hx, (heval x (hBA hx)).mpr hx⟩⟩
  rwa [he] at h

end BoundedSetPredicate
end PolishSpaceBook.SetTheoryModels
