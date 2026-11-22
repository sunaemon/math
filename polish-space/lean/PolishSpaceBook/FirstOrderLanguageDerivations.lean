module

public import PolishSpaceBook.FirstOrderLanguageMap

@[expose] public section

/-!
# Transport of proofs and the new Henkin axioms

Proof transport is an induction on the displayed natural-deduction rules. The
new constant symbols come from mathlib's language extension, not from variable
names; closedness of the witness axioms is checked explicitly. Conservativity
of the extension is a separate assertion from the forward transport proved here.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v u' v' w
variable {L : Language.{u,v}} {K : Language.{u',v'}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
local instance : DecidableEq (AlphaFormula K) := Classical.decEq _

namespace Context

def mapLanguage (f : L →ᴸ K) (Γ : Context L) : Context K := Γ.image (AlphaFormula.mapLanguage f)

@[simp] theorem mapLanguage_insert (f : L →ᴸ K) (Γ : Context L) (φ : AlphaFormula L) :
    (insert φ Γ).mapLanguage f = insert (φ.mapLanguage f) (Γ.mapLanguage f) := by
  simp [mapLanguage]

@[simp] theorem fv_mapLanguage (f : L →ᴸ K) (Γ : Context L) : (Γ.mapLanguage f).fv = Γ.fv := by
  ext x
  constructor
  · intro hx
    obtain ⟨ψ, hψ, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
    exact mem_fv_of_mem hφ (by simpa using hx)
  · intro hx
    obtain ⟨φ, hφ, hx⟩ := Finset.mem_biUnion.mp hx
    exact mem_fv_of_mem (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩) (by simpa using hx)

end Context
namespace Derives

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Language inclusion
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now induct on the derivation. Each rule maps to the same rule in the larger language. Implication introduction,
    disjunction elimination, and existential elimination map an added hypothesis to its image. Quantifier
    instantiation and equality elimination use the substitution identity. The free-variable identity, also for
    finite contexts, preserves every eigenvariable condition. Finally, a theory derivation uses a finite context,
    whose image is still a finite subset of the image theory.
    \end{proof}
-/
theorem mapLanguage {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ) (f : L →ᴸ K) :
    Derives (Γ.mapLanguage f) (φ.mapLanguage f) := by
  induction h with
  | hyp Γ φ => simpa using hyp (Γ.mapLanguage f) (φ.mapLanguage f)
  | andIntro hφ hψ ihφ ihψ => simpa using andIntro ihφ ihψ
  | andLeft h ih => exact andLeft (by simpa using ih)
  | andRight h ih => exact andRight (by simpa using ih)
  | orLeft ψ h ih => simpa using orLeft (ψ.mapLanguage f) ih
  | orRight φ h ih => simpa using orRight (φ.mapLanguage f) ih
  | orElim hd hl hr ihd ihl ihr =>
    exact orElim (by simpa using ihd) (by simpa using ihl) (by simpa using ihr)
  | impIntro h ih => simpa using impIntro (by simpa using ih)
  | impElim hf ha ihf iha => exact impElim (by simpa using ihf) iha
  | falseElim φ h ih => exact falseElim _ (by simpa using ih)
  | allIntro x h hx ih => simpa using allIntro x ih (by simpa using hx)
  | allElim x φ t h ih =>
    simpa using allElim x (φ.mapLanguage f) (f.onTerm t) (by simpa using ih)
  | exIntro x φ t h ih =>
    simpa using exIntro x (φ.mapLanguage f) (f.onTerm t) (by simpa using ih)
  | exElim x y φ χ he hc hy ihe ihc =>
    simpa using exElim x y (φ.mapLanguage f) (χ.mapLanguage f)
      (by simpa using ihe) (by simpa using ihc) (by simpa using hy)
  | eqIntro Γ t => simpa using eqIntro (Γ.mapLanguage f) (f.onTerm t)
  | eqElim φ x t r ht he iht ihe =>
    simpa using eqElim (φ.mapLanguage f) x (f.onTerm t) (f.onTerm r)
      (by simpa using iht) (by simpa using ihe)
  | excludedMiddle Γ φ => simpa [neg] using excludedMiddle (Γ.mapLanguage f) (φ.mapLanguage f)

end Derives

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now induct on the derivation. Each rule maps to the same rule in the larger language. Implication introduction,
    disjunction elimination, and existential elimination map an added hypothesis to its image. Quantifier
    instantiation and equality elimination use the substitution identity. The free-variable identity, also for
    finite contexts, preserves every eigenvariable condition. Finally, a theory derivation uses a finite context,
    whose image is still a finite subset of the image theory.
    \end{proof}
-/
theorem ProvesFrom.mapLanguage {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom T φ) (f : L →ᴸ K) : ProvesFrom (AlphaFormula.mapLanguage f '' T) (φ.mapLanguage f) := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  refine ⟨Γ.mapLanguage f, ?_, hd.mapLanguage f⟩
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hψ
  exact ⟨χ, hΓ χ hχ, rfl⟩

namespace AlphaFormula

theorem fv_subst (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).fv = φ.fv.erase x ∪ if x ∈ φ.fv then t.varFinset else ∅ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.fv_subst φ x t

/-- One new constant supplies a witness to an old one-variable formula. -/
def henkinAxiom {A : Type w} (a : A) (x : ℕ) (φ : AlphaFormula L) : AlphaFormula L[[A]] :=
  let ψ := φ.mapLanguage (L.lhomWithConstants A)
  binary .imp (quant .ex x ψ) (ψ.subst x (L.con a).term)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    At each stage, the \termuse{language inclusion lemma} lets us use the old terms, formulas, and derivations in
    the expanded language. Each new constant is a closed term, so the free-variable substitution formula gives
    $$\begin{aligned}
    &\FreeVars{(\existsbind{x}{\psi})\to\psi\subst{x}{c_{n,\psi,x}}}\\
    &\qquad=\SetDifference{\FreeVars{\psi}}{\{x\}}=\varnothing.
    \end{aligned}$$
    Thus every added Henkin axiom is a sentence.
-/
@[simp] theorem fv_henkinAxiom {A : Type w} (a : A) (x : ℕ) (φ : AlphaFormula L) :
    (henkinAxiom a x φ).fv = φ.fv.erase x := by
  simp [henkinAxiom, fv_subst, Constants.term, Term.varFinset]

theorem henkinAxiom_sentence {A : Type w} (a : A) (x : ℕ) (φ : AlphaFormula L)
    (hφ : φ.fv ⊆ {x}) : henkinAxiom a x φ ∈ Sentences L[[A]] := by
  change (henkinAxiom a x φ).fv = ∅
  rw [fv_henkinAxiom]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hy
  exact hyx (Finset.mem_singleton.mp (hφ hy))

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
