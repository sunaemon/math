module

public import PolishSpaceBook.PCACases
public import PolishSpaceBook.PCACurrying
public import PolishSpaceBook.TriposToposForcingRealizability

@[expose] public section

/-! # Uniform entailment and propositional operations over any PCA -/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open Expression
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)
variable {I : Type v}

def Entails (φ ψ : RealizabilityPredicate A I) : Prop :=
  ∃ r, ∀ i a, a ∈ φ i → ∃ b, K.application r a = Part.some b ∧ b ∈ ψ i

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    **The realizability tripos over a PCA.** Fix a PCA $A$ with $U$-small carrier and put
    $$\mathcal P_A(I):=\funcspace{I}{\PowerSet{A}}.$$
    Write $\varphi\le\psi$ when one $r\in A$ satisfies
    $r\cdot a\downarrow\in\psi(i)$ for every $i\in I$ and $a\in\varphi(i)$.
    Use the pairing and selectors constructed in §{sec:realizability-assemblies} to define
    $$\begin{aligned}
    \top(i)&:=A,\qquad \bot(i):=\emptyset,\\
    (\varphi\land\psi)(i)&:=\{\PCAPair{a}{b}:a\in\varphi(i),\ b\in\psi(i)\},\\
    (\varphi\lor\psi)(i)&:=\{\PCAPair{\mathsf k}{a}:a\in\varphi(i)\}\\
    &\qquad\cup\{\PCAPair{\mathsf q}{b}:b\in\psi(i)\},\\
    (\varphi\to\psi)(i)&:=\{r\in A:\forall a\in\varphi(i),\ r\cdot a\downarrow\in\psi(i)\}.
    \end{aligned}$$
    Here the tags are the two selector elements of the PCA; no natural-number structure on $A$ is assumed.
-/
def predAnd (φ ψ : RealizabilityPredicate A I) : RealizabilityPredicate A I :=
  fun i => {w | ∃ a b, w = K.pair a b ∧ a ∈ φ i ∧ b ∈ ψ i}

def predOr (φ ψ : RealizabilityPredicate A I) : RealizabilityPredicate A I :=
  fun i => {w | (∃ a, w = K.pair K.k a ∧ a ∈ φ i) ∨
    (∃ b, w = K.pair K.secondSelector b ∧ b ∈ ψ i)}

def predImp (φ ψ : RealizabilityPredicate A I) : RealizabilityPredicate A I :=
  fun i => {r | ∀ a, a ∈ φ i → ∃ b, K.application r a = Part.some b ∧ b ∈ ψ i}

theorem entails_refl (φ : RealizabilityPredicate A I) : K.Entails φ φ :=
  ⟨K.identity,fun _ a ha => ⟨a,K.application_identity a,ha⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The identity combinator proves reflexivity. Given successive trackers $r,s$, the element
    $\PCAAbstract{a}{s(ra)}$ proves transitivity. The identity also tracks reduction to $\top$ and reduction
    from $\bot$, the latter vacuously.
-/
theorem entails_trans {φ ψ θ : RealizabilityPredicate A I} (h : K.Entails φ ψ) (h' : K.Entails ψ θ) :
    K.Entails φ θ := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := h'
  refine ⟨K.composition r s,fun i a ha => ?_⟩
  obtain ⟨b,hb,hb'⟩ := hr i a ha
  obtain ⟨c,hc,hc'⟩ := hs i b hb'
  refine ⟨c,?_,hc'⟩
  rw [K.application_composition,hb,Part.bind_some,hc]

theorem entails_top (φ : RealizabilityPredicate A I) : K.Entails φ (fun _ => Set.univ) :=
  ⟨K.identity,fun _ a _ => ⟨a,K.application_identity a,Set.mem_univ a⟩⟩

theorem bot_entails (φ : RealizabilityPredicate A I) : K.Entails (fun _ => ∅) φ :=
  ⟨K.identity,fun _ _ h => h.elim⟩

theorem and_left (φ ψ : RealizabilityPredicate A I) : K.Entails (K.predAnd φ ψ) φ := by
  refine ⟨K.firstProjection,?_⟩
  rintro i _ ⟨a,b,rfl,ha,_⟩
  exact ⟨a,K.application_firstProjection a b,ha⟩

theorem and_right (φ ψ : RealizabilityPredicate A I) : K.Entails (K.predAnd φ ψ) ψ := by
  refine ⟨K.secondProjection,?_⟩
  rintro i _ ⟨a,b,rfl,_,hb⟩
  exact ⟨b,K.application_secondProjection a b,hb⟩

theorem and_intro {φ ψ θ : RealizabilityPredicate A I} (h : K.Entails θ φ) (h' : K.Entails θ ψ) :
    K.Entails θ (K.predAnd φ ψ) := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := h'
  refine ⟨K.paired r s,fun i a ha => ?_⟩
  obtain ⟨b,hb,hb'⟩ := hr i a ha
  obtain ⟨c,hc,hc'⟩ := hs i a ha
  exact ⟨K.pair b c,K.application_paired hb hc,b,c,rfl,hb',hc'⟩

theorem or_left (φ ψ : RealizabilityPredicate A I) : K.Entails φ (K.predOr φ ψ) :=
  ⟨K.pairLeft K.k,fun _ a ha => ⟨K.pair K.k a,K.application_pairLeft K.k a,Or.inl ⟨a,rfl,ha⟩⟩⟩

theorem or_right (φ ψ : RealizabilityPredicate A I) : K.Entails ψ (K.predOr φ ψ) :=
  ⟨K.pairLeft K.secondSelector,fun _ a ha =>
    ⟨K.pair K.secondSelector a,K.application_pairLeft K.secondSelector a,Or.inr ⟨a,rfl,ha⟩⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For conjunction, the two projections eliminate a pair, and trackers $r,s$ with a common source combine as
    $\PCAAbstract{a}{\mathsf p(ra)(sa)}$. For disjunction, the injections are tracked by $\mathsf p\mathsf k$
    and $\mathsf p\mathsf q$. The eliminator for trackers $r,s$ is
    $$\PCAAbstract{w}{\bigl((\mathsf l w)r s\bigr)(\mathsf r w)}.$$
    The tag selects the appropriate tracker before it receives the payload, so the unused branch need not be
    defined on that input. These are the meet and join universal properties.
-/
theorem or_elim {φ ψ θ : RealizabilityPredicate A I} (h : K.Entails φ θ) (h' : K.Entails ψ θ) :
    K.Entails (K.predOr φ ψ) θ := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := h'
  refine ⟨K.casesTracker r s,?_⟩
  rintro i _ (⟨a,rfl,ha⟩ | ⟨b,rfl,hb⟩)
  · obtain ⟨c,hc,hc'⟩ := hr i a ha
    exact ⟨c,(K.application_casesTracker_left r s a).trans hc,hc'⟩
  · obtain ⟨c,hc,hc'⟩ := hs i b hb
    exact ⟨c,(K.application_casesTracker_right r s b).trans hc,hc'⟩

def uncurrying (r : A) : A := K.abstractElement
  (.app (.app (.const r) (.app (.const K.firstProjection) (.var (none : Option Empty))))
    (.app (.const K.secondProjection) (.var none))) Empty.elim

theorem application_uncurrying (r a b : A) :
    K.application (K.uncurrying r) (K.pair a b) =
      (K.application r a).bind (fun s => K.application s b) := by
  rw [uncurrying,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none,
    application_firstProjection,application_secondProjection]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For implication, a tracker $r$ of $\theta\land\varphi\le\psi$ gives
    $$\PCAAbstract{a,b}{r(\PCAPair{a}{b})}$$
    as a tracker of $\theta\le(\varphi\to\psi)$: the first application is always defined and returns a tracker
    of the required implication. Conversely, a tracker $r$ of the latter reduction gives
    $$\PCAAbstract{w}{\bigl(r(\mathsf l w)\bigr)(\mathsf r w)}$$
    for the former. This proves the implication adjunction, including definedness on the required inputs.
-/
theorem imp_adjunction (θ φ ψ : RealizabilityPredicate A I) :
    K.Entails (K.predAnd θ φ) ψ ↔ K.Entails θ (K.predImp φ ψ) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨K.currying r,fun i a ha => ⟨K.specialized r a,K.application_currying r a,?_⟩⟩
    intro b hb
    obtain ⟨c,hc,hc'⟩ := hr i (K.pair a b) ⟨a,b,rfl,ha,hb⟩
    exact ⟨c,(K.application_specialized r a b).trans hc,hc'⟩
  · rintro ⟨r,hr⟩
    refine ⟨K.uncurrying r,?_⟩
    rintro i _ ⟨a,b,rfl,ha,hb⟩
    obtain ⟨s,hs,hs'⟩ := hr i a ha
    obtain ⟨c,hc,hc'⟩ := hs' b hb
    refine ⟨c,?_,hc'⟩
    rw [K.application_uncurrying,hs,Part.bind_some,hc]

theorem reindex_entails {J : Type*} (f : I → J) {φ ψ : RealizabilityPredicate A J}
    (h : K.Entails φ ψ) : K.Entails (realizabilityReindex f φ) (realizabilityReindex f ψ) :=
  ⟨h.choose,fun i => h.choose_spec (f i)⟩

end PolishSpaceBook.PartialCombinatoryAlgebra
