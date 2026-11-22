module

public import PolishSpaceBook.LambdaBasicRealizers
public import PolishSpaceBook.ComputablePolishSpacesTTE

@[expose] public section

/-!
# Represented-space realizers computed by lambda terms

The public predicate uses the closed lambda-program definition directly.
The legacy oracle-recursive development is not imported here.
-/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    *   \termdefine{continuously realizable} if some continuous $F$ realizes it;
    *   \termdefine{computably realizable} if some \termuse{Type-Two lambda realizer} computes such an $F$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A function $f:X\to Y$ between \termuseas{computable Polish space}{computable Polish spaces} is
    computable iff there is a Type-Two lambda realizer which transforms every fast Cauchy name of $x$ into a fast Cauchy
    name of $f(x)$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The \termuse{Cauchy representation} in §{sec:cauchy-representation-admissibility} was purely topological: a name was an
    element of
    $\BaireSpace$ coding a fast Cauchy sequence, and a continuous translator between name spaces witnessed reducibility of
    representations. **\termdefineas{Type-Two Effectivity}{Type-2 Theory of Effectivity}** (TTE) adds the algorithmic
    requirement: names are input functions $p:\NN\to\NN$, and a realizer is a lambda program transforming names into names.
    The program obtains information from an input name by querying its entries as needed.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    This is the operational form of computable analysis. A real number is computable when it has a computable
    \termuse{Cauchy name}; a function is computable when there is a single lambda realizer which, given any name for an
    input as a function argument, produces a name for the output.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For representations $\delta_X,\delta_Y$, a partial name map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ realizes
    $f:X\to Y$ when its domain contains $\DomainOf{\delta_X}$, its values there belong to $\DomainOf{\delta_Y}$, and
    $$\delta_Y(F(p))=f(\delta_X(p))\qquad(p\in\DomainOf{\delta_X}).$$
    The function $f$ is \termdefineas{computable function between represented spaces}{computable} if such an $F$ has a
    Type-Two lambda realizer. Thus $F$ is the map between names, and the closed lambda term is the program computing it. One
    program must work for every name of every input point.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For Polish spaces with a chosen computable metric presentation, the representation $\rho_X$ used in
    §{sec:cauchy-representation-admissibility} takes a name to the
    limit of a fast Cauchy sequence in a fixed computable dense set. Thus a computable real is a real with a computable fast
    Cauchy name, and a computable function between Polish spaces is one whose action on such names is computed by a lambda
    realizer with the input name as a function argument.
-/
def HasComputableRealizer (δX : Representation X) (δY : Representation Y) (f : X → Y) : Prop :=
  ∃ F : δX.domain → δY.domain,
    TypeTwoComputable (fun p => (F p).val) ∧ Realizes δX δY F f

/-- Identity on names is realized by the closed identity lambda term. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Apply this substitution to realizers and the preceding realization identity. Identity and composition are therefore
    computably realizable, so represented spaces and computably realizable maps form a category. The composition
    construction uses only the specified name domains; no behavior is required on names outside them.
-/
theorem hasComputableRealizer_id (δX : Representation X) :
    HasComputableRealizer δX δX (id : X → X) :=
  ⟨id, ⟨NamedLambda.AlphaTerm.identityProgram, identityProgram_computes δX.domain⟩,
    fun _ => rfl⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: corollary
  title: Continuity of computably realizable maps
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Finite use makes the name realizer continuous on the input representation's domain. Composing it with the continuous output representation gives the original map composed with the input representation. The input representation is a quotient map by topology recovery in §{sec:kreitz-weihrauch-admissibility}, so continuity descends to the represented spaces.
-/
theorem HasComputableRealizer.continuous [TopologicalSpace X] [SequentialSpace X]
    [TopologicalSpace Y] {δX : Representation X} {δY : Representation Y} {f : X → Y}
    (hf : HasComputableRealizer δX δY f) (hX : δX.IsAdmissible) (hY : δY.IsContinuous) :
    Continuous f := by
  obtain ⟨F, hF, hf⟩ := hf
  have hFc : Continuous F := hF.continuous.subtype_mk _
  apply (isQuotientMap_of_admissible δX hX).continuous_iff.mpr
  have he : f ∘ δX.toFun = δY.toFun ∘ F := funext fun p => (hf p).symm
  rw [he]
  exact hY.comp hFc

/-- A domain restriction keeps the very same closed lambda program. -/
theorem TypeTwoComputes.restrict {D E : Set (ℕ → ℕ)} (hED : E ⊆ D)
    {F : D → (ℕ → ℕ)} {P : NamedLambda.AlphaTerm} (h : TypeTwoComputes P F) :
    TypeTwoComputes P (fun p : E => F ⟨p.val, hED p.property⟩) :=
  ⟨h.1, fun p n m => h.2 ⟨p.val, hED p.property⟩ n m⟩

/-- Realizer composition uses the explicit lambda composition term. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Apply this substitution to realizers and the preceding realization identity. Identity and composition are therefore
    computably realizable, so represented spaces and computably realizable maps form a category. The composition
    construction uses only the specified name domains; no behavior is required on names outside them.
-/
theorem HasComputableRealizer.comp {Z : Type*}
    {δX : Representation X} {δY : Representation Y} {δZ : Representation Z}
    {f : X → Y} {g : Y → Z} (hg : HasComputableRealizer δY δZ g)
    (hf : HasComputableRealizer δX δY f) : HasComputableRealizer δX δZ (g ∘ f) := by
  obtain ⟨G, ⟨P, hP⟩, hG⟩ := hg
  obtain ⟨F, ⟨Q, hQ⟩, hF⟩ := hf
  exact ⟨G ∘ F, ⟨NamedLambda.AlphaTerm.compositionProgram P Q, hP.comp hQ⟩,
    fun p => (hG (F p)).trans (congrArg g (hF p))⟩
end PolishSpaceBook
