module

public import PolishSpaceBook.FirstOrderCompleteness

@[expose] public section

/-!
# Conservativity from model expansions

We use mathlib's symbol-preserving expansion predicate. Every old countermodel
can be expanded, so soundness rules out a new proof of an old-language sentence.
Completeness supplies the countermodel; uniqueness of expansion is not needed
for this implication and is proved separately for definitions.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v u' v' w
variable {L : Language.{u,v}} {K : Language.{u',v'}}

/-- Equality of structures is equality of the interpretations of all symbols. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Semantics.** A \termdefineas{structure for a language}{structure} for a language $L$ is the data needed to interpret
    the symbols of $L$. It consists of a nonempty set $M$, called the \termdefineas{domain of structure}{domain} or
    \termdefineas{underlying set of structure}{underlying set}, together with interpretations of the non-logical symbols:
    each $n$-ary relation symbol $R$ is interpreted as a subset $R^{\mathcal M} \IncludedIn \seqPower{M}{n}$, and each
    $n$-ary
    function symbol $f$ as a function $f^{\mathcal M} : \seqPower{M}{n} \to M$. For a $0$-ary function symbol $c$, this is
    equivalently an element $c^{\mathcal M} \in M$. For $L_\in$, a structure is just a pair $\mathcal M=(M,E)$ with
    $E\IncludedIn M\times M$ interpreting $\in$.
-/
theorem structure_ext {M : Type w} (A B : L.Structure M)
    (hf : ∀ n (f : L.Functions n) s, @Structure.funMap L M A n f s = @Structure.funMap L M B n f s)
    (hr : ∀ n (R : L.Relations n) s, @Structure.RelMap L M A n R s = @Structure.RelMap L M B n R s) : A = B := by
  cases A
  cases B
  congr 1 <;> funext n r s
  · exact hf n r s
  · exact hr n r s

/-- An expansion has exactly the original structure as its reduct. -/
theorem reduct_eq_of_expansion (f : L →ᴸ K) (M : Type w) [old : L.Structure M] [K.Structure M]
    [f.IsExpansionOn M] : f.reduct M = old := by
  apply structure_ext
  · intro n F s
    exact f.map_onFunction F s
  · intro n R s
    exact f.map_onRelation R s

theorem AlphaFormula.mapLanguage_realize_expansion (f : L →ᴸ K) {M : Type w}
    [L.Structure M] [K.Structure M] [f.IsExpansionOn M] (φ : AlphaFormula L) (s : ℕ → M) :
    (φ.mapLanguage f).Realize s ↔ φ.Realize s := by
  have h := φ.mapLanguage_realize_reduct f s
  rwa [reduct_eq_of_expansion f M] at h

/-- Sentence theories are satisfied under every assignment. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A structure $\mathcal M$ is a \termdefineas{model of a theory}{model} of a theory $T$, written $\mathcal M\models T$,
    when every axiom of $T$ is true in $\mathcal M$ under the satisfaction relation defined below. Thus every model is a
    structure, but not every structure is a model of the theory under discussion. This is why model-theoretic theorems such
    as downward Löwenheim--Skolem are stated for arbitrary structures, even though the forcing application in
    §{sec:internal-model-closure} applies them to structures that are already models of a fragment of ZFC.
-/
def TheoryRealize {M : Type w} (A : L.Structure M) (T : Set (AlphaFormula L)) : Prop :=
  ∀ (s : ℕ → M) φ, φ ∈ T → @AlphaFormula.Realize L M A φ s

/-- Expanding every old model suffices for conservativity over old sentences. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Model-expansion criterion
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Suppose an $L$-sentence $\sigma$ is provable from $T'$ but not from $T$.
    Completeness gives a nonempty model $\mathcal M\models T$ with $\mathcal M\not\models\sigma$.
    By hypothesis it has an expansion $\mathcal M'\models T'$ with the same domain and old interpretations.
    Induction on terms and formulas shows that the expansion and its reduct agree on $L$-formulas,
    so $\mathcal M'\not\models\sigma$. This contradicts soundness applied to the proof from $T'$.
    Uniqueness of the expansion is not needed for this argument.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Conservativity.**
    An extension of $T$ is \termdefineas{conservative extension}{conservative} if every old-language sentence provable
    in the extension is already provable from $T$. The following criterion separates this property from uniqueness
    of model expansions.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Semantics.** A \termdefineas{structure for a language}{structure} for a language $L$ is the data needed to interpret
    the symbols of $L$. It consists of a nonempty set $M$, called the \termdefineas{domain of structure}{domain} or
    \termdefineas{underlying set of structure}{underlying set}, together with interpretations of the non-logical symbols:
    each $n$-ary relation symbol $R$ is interpreted as a subset $R^{\mathcal M} \IncludedIn \seqPower{M}{n}$, and each
    $n$-ary
    function symbol $f$ as a function $f^{\mathcal M} : \seqPower{M}{n} \to M$. For a $0$-ary function symbol $c$, this is
    equivalently an element $c^{\mathcal M} \in M$. For $L_\in$, a structure is just a pair $\mathcal M=(M,E)$ with
    $E\IncludedIn M\times M$ interpreting $\in$.
-/
theorem conservative_of_model_expansion (f : L →ᴸ K) {T : Set (AlphaFormula L)}
    {U : Set (AlphaFormula K)} (hT : T ⊆ Sentences L)
    (hexpand : ∀ (M : Type (max u v)) (A : L.Structure M), Nonempty M → TheoryRealize A T →
      ∃ B : K.Structure M, @LHom.IsExpansionOn L K f M A B ∧ TheoryRealize B U)
    {σ : AlphaFormula L} (hσ : σ ∈ Sentences L) (hp : ProvesFrom U (σ.mapLanguage f)) : ProvesFrom T σ := by
  by_contra hn
  obtain ⟨M, A, hne, hmodel, hfalse⟩ := exists_countermodel_of_not_proves hT hσ hn
  obtain ⟨B, hB, hU⟩ := hexpand M A hne hmodel
  let := A
  let := B
  let : f.IsExpansionOn M := hB
  let s : ℕ → M := fun _ => Classical.choice hne
  have ht := hp.sound s (hU s)
  exact hfalse s ((σ.mapLanguage_realize_expansion f s).mp ht)

end PolishSpaceBook.NamedFirstOrder
