module

public import PolishSpaceBook.FirstOrderFunctionDefinitions

@[expose] public section

/-!
# Conservativity of mixed and successive definitions

Relation and function definitions reuse their individual model-expansion proofs.
Conservativity composes by pulling an old-language sentence back through each
stage. Induction records the same argument for any finite number of stages.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v u' v' u'' v'' z z'
variable {L : Language.{u,v}} {K : Language.{u',v'}} {J : Language.{u'',v''}}

/-- Conservativity is transitive along composable language maps. -/
theorem conservative_comp (f : L →ᴸ K) (g : K →ᴸ J)
    {T : Set (AlphaFormula L)} {U : Set (AlphaFormula K)} {V : Set (AlphaFormula J)}
    (hf : ∀ σ ∈ Sentences L, ProvesFrom U (σ.mapLanguage f) → ProvesFrom T σ)
    (hg : ∀ τ ∈ Sentences K, ProvesFrom V (τ.mapLanguage g) → ProvesFrom U τ)
    {σ : AlphaFormula L} (hσ : σ ∈ Sentences L)
    (hp : ProvesFrom V (σ.mapLanguage (g.comp f))) : ProvesFrom T σ := by
  apply hf σ hσ
  apply hg (σ.mapLanguage f)
  · simpa only [Sentences, Set.mem_ofPred_eq, fv_mapLanguage] using hσ
  · simpa only [mapLanguage_comp] using hp

/-- Relation definitions may be followed by functions whose graphs use those relations.
Constants are the arity-zero members of the function family. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: corollary
  title: Conservativity of definitional extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    In each case every old model admits an expansion satisfying the new axioms, so the
    \termuse{model-expansion criterion for conservativity} applies. To combine relation definitions with function
    definitions, first add the relations and then the functions, including constants as the nullary case.
    The defining graphs may use the relations already added, provided the intermediate theory proves their
    unique-existence assertions. A sentence of the original language provable in the final theory is first
    provable in the intermediate theory, by conservativity of the function definitions, and then in $T$,
    by conservativity of the relation definitions.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Mathematical writing almost never stays in the bare language in which a theory is first stated. Set theory is the main
    example in this book. Officially ZFC is written in $L_\in$, whose only non-logical symbol is $\in$, but ordinary
    set-theoretic prose uses $\emptyset$, $\{a,b\}$, $\bigcup x$, ordered pairs, functions, domains, restrictions, products,
    and many other notations. The mechanism that justifies this practice is
    \termdefineas{definitional extension}{extension by definition}. It adds names for objects, operations, or relations
    that the old theory already
    defines uniquely, and it does not create new theorems in the old language.
-/
theorem conservative_relation_function_definitions {ι : ℕ → Type z} {κ : ℕ → Type z'}
    (R : RelationDefinitions L ι) (F : FunctionDefinitions (L.sum (relationSymbols ι)) κ)
    {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hF : ∀ n (f : κ n), ProvesFrom (R.theory T) (F.uniqueExistence f))
    {σ : AlphaFormula L} (hσ : σ ∈ Sentences L)
    (hp : ProvesFrom (F.theory (R.theory T))
      (σ.mapLanguage (FunctionDefinitions.inclusion.comp RelationDefinitions.inclusion))) :
    ProvesFrom T σ :=
  conservative_comp RelationDefinitions.inclusion FunctionDefinitions.inclusion
    (fun _ h => R.conservative hT h) (fun _ h => F.conservative (R.theory_sentences hT) hF h) hσ hp

/-- The inclusion from the initial language to a given stage. -/
def languageChainMap {Λ : ℕ → Language.{u,v}} (f : ∀ n, Λ n →ᴸ Λ (n + 1)) :
    (n : ℕ) → Λ 0 →ᴸ Λ n
  | 0 => LHom.id _
  | n + 1 => (f n).comp (languageChainMap f n)

/-- Pull a sentence back through any finite sequence of conservative extensions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    More generally, let $T_0,\ldots,T_n$ be successive theories obtained by such definitions, and let $\sigma$
    be a sentence of the language of $T_0$. For $n=0$ there is nothing to prove. If $n\ge 1$ and $T_n\vdash\sigma$,
    conservativity of the last extension gives
    $T_{n-1}\vdash\sigma$. Repeating this step gives $T_0\vdash\sigma$. Induction on $n$ therefore handles
    any finite succession of definitions, each allowed to use the symbols introduced earlier.
-/
theorem conservative_chain {Λ : ℕ → Language.{u,v}} (f : ∀ n, Λ n →ᴸ Λ (n + 1))
    (T : ∀ n, Set (AlphaFormula (Λ n)))
    (hstep : ∀ n σ, σ ∈ Sentences (Λ n) →
      ProvesFrom (T (n + 1)) (σ.mapLanguage (f n)) → ProvesFrom (T n) σ)
    (n : ℕ) {σ : AlphaFormula (Λ 0)} (hσ : σ ∈ Sentences (Λ 0))
    (hp : ProvesFrom (T n) (σ.mapLanguage (languageChainMap f n))) : ProvesFrom (T 0) σ := by
  induction n with
  | zero => simpa only [languageChainMap, mapLanguage_id] using hp
  | succ n ih =>
    apply ih
    apply hstep n (σ.mapLanguage (languageChainMap f n))
    · simpa only [Sentences, Set.mem_ofPred_eq, fv_mapLanguage] using hσ
    · simpa only [languageChainMap, mapLanguage_comp] using hp

end PolishSpaceBook.NamedFirstOrder
