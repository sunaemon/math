module

public import PolishSpaceBook.LambdaFunctionSpaces
public import PolishSpaceBook.RepresentedContinuousProducts

@[expose] public section

/-! # Continuous currying for lambda-coded function names

The same representation as the computable exponential law is used throughout.
Only the retained name may be noncomputable; the reassociation program is fixed.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaFunction
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Reassociate a triple using only the already constructed lambda projections. -/
def associateName (w : ℕ → ℕ) : ℕ → ℕ :=
  typeTwoPairName (typeTwoLeftName (typeTwoLeftName w))
    (typeTwoPairName (typeTwoRightName (typeTwoLeftName w)) (typeTwoRightName w))

def associateProgram : AlphaTerm :=
  pairOutputProgram (projectOutputProgram true leftProgram)
    (pairOutputProgram (projectOutputProgram false leftProgram) rightProgram)

theorem associateProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes associateProgram (fun p : D => associateName p.val) :=
  (leftProgram_computes D).left.pair
    ((leftProgram_computes D).right.pair (rightProgram_computes D))

def continuousCurryProgram (P : AlphaTerm) : AlphaTerm := compositionProgram P associateProgram

theorem continuousCurryProgram_closed {P : AlphaTerm} (hP : P.Closed) :
    (continuousCurryProgram P).Closed :=
  compositionProgram_closed hP (associateProgram_computes Set.univ).1

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    With the projection terms $L,R$ from the evaluation proof, put
    $$A:=\LambdaPairOutputs{\LambdaProjectOutput{1}{L}}{
    \LambdaPairOutputs{\LambdaProjectOutput{2}{L}}{R}},
    \qquad c':=C_{c,A}.$$
    On a name $\langle\langle r,p\rangle,q\rangle$, the three projections read $r,p,q$ and the two pairings produce $\langle r,\langle p,q\rangle\rangle$. Thus the fixed closed term $A$ changes only the brackets in this triple of names. The composition lemma carries every required output of $c$ on the latter name to an output of $c'$ on the former name. Confluence excludes a different numeral output. The term $c'$ is closed and is fixed before $r,p,q$ are supplied. On named syntax codes, its construction inserts the code of $c$ into one fixed composition template. §{sec:lambda-function-code-transforms} proves that this operation is primitive recursive and gives its closed lambda implementation.
-/
theorem continuousCurryProgram_runs {P : AlphaTerm} (hP : P.Closed)
    (r p q : ℕ → ℕ) {n m : ℕ}
    (h : OracleRuns (typeTwoPairName r (typeTwoPairName p q)) P n m) :
    OracleRuns (typeTwoPairName (typeTwoPairName r p) q) (continuousCurryProgram P) n m := by
  apply compositionProgram_runs hP (associateProgram_computes Set.univ).1 h
  intro k
  simpa only [associateName, typeTwoLeft_pair, typeTwoRight_pair] using
    (typeTwoComputes_iff_runs.mp (associateProgram_computes Set.univ)).2
      ⟨typeTwoPairName (typeTwoPairName r p) q, Set.mem_univ _⟩ k

/-- The chosen syntax index is fixed independently of the parameter name. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $e'$ be the index of $c'$. Given a name $p$ of a parameter point $z$, output the function name $e'\concat\langle r,p\rangle$. On an argument name $q$, its program computes precisely $G(\langle p,q\rangle)$, so the name represents the section $x\mapsto g(z,x)$. This section is continuously realizable by finite use with its auxiliary oracle fixed. Since $G$ realizes $g$, different names of $z$ produce names of the same section.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The same function-space representation also supports currying for continuous realizers. Here the auxiliary oracle coding
    the original realizer must be retained together with the parameter name.
-/
theorem functionNameRealizes_continuous_section {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    {G : (typeTwoProductRepresentation δZ δX).domain → δY.domain}
    (r : ℕ → ℕ) (P : AlphaTerm) (hP : P.Closed) (e : ℕ)
    (he : Term.closedProgram e = continuousCurryProgram P)
    (hc : ∀ w n, OracleRuns (typeTwoPairName r w.val) P n ((G w).val n))
    (hg : Realizes (typeTwoProductRepresentation δZ δX) δY G g) (p : δZ.domain) :
    FunctionNameRealizes δX δY (typeTwoTagName e (typeTwoPairName r p.val))
      (fun x => g (δZ.toFun p, x)) := by
  let F : δX.domain → δY.domain := fun q =>
    G ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩
  refine ⟨F, ?_, ?_⟩
  · intro q n
    simp only [typeTwoTail_tag, functionNameProgram, typeTwoTagName, he]
    exact continuousCurryProgram_runs hP r p.val q.val
      (hc ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩ n)
  · intro q
    simpa only [F, typeTwoProductRepresentation, typeTwoLeft_pair, typeTwoRight_pair] using
      hg ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩

theorem continuous_realizer_section {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY g) (z : Z) :
    HasContinuousRealizer δX δY (fun x => g (z, x)) := by
  obtain ⟨G, hG, hg⟩ := hg
  obtain ⟨r, P, hP, hc⟩ :=
    (LambdaContinuousCode.continuous_iff_exists_parameter (fun w => (G w).val)).mp hG
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ (continuousCurryProgram_closed hP)
  obtain ⟨p, rfl⟩ := δZ.surjective z
  exact (functionNameRealizes_continuous_section r P hP e he hc hg p).continuous

def continuousCurryMap {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY g)
    (z : Z) : ContinuouslyRealizableMap δX δY :=
  ⟨fun x => g (z, x), continuous_realizer_section hg z⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Continuous-realizer exponential law
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The name transformation $p\mapsto e'\concat\langle r,p\rangle$ is continuous: its first coordinate is constant, and each later coordinate pairs a fixed auxiliary digit with one input digit. This gives a continuous realizer of the section map. It need not be computable when $r$ is noncomputable.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Choose a continuous realizer $G$ of $g$. Apply oracle coding once to this entire partial name map, obtaining one
    auxiliary oracle $r$ and one finite program $c$. Thus, on a paired input name $\langle p,q\rangle$, the program computes
    the output of $G$ using the oracle $\langle r,\langle p,q\rangle\rangle$. The choices of $r$ and $c$ are fixed before
    the parameter name $p$ is supplied.
-/
theorem continuous_curry {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY g) :
    HasContinuousRealizer δZ (typeTwoFunctionRepresentation δX δY) (continuousCurryMap hg) := by
  obtain ⟨G, hG, hg⟩ := hg
  obtain ⟨r, P, hP, hc⟩ :=
    (LambdaContinuousCode.continuous_iff_exists_parameter (fun w => (G w).val)).mp hG
  obtain ⟨e, he⟩ := Term.closedProgram_surjective _ (continuousCurryProgram_closed hP)
  have hs (p : δZ.domain) := functionNameRealizes_continuous_section r P hP e he hc hg p
  let H : δZ.domain → (typeTwoFunctionRepresentation δX δY).domain := fun p =>
    ⟨typeTwoTagName e (typeTwoPairName r p.val),
      ⟨continuousCurryMap ⟨G, hG, hg⟩ (δZ.toFun p), hs p⟩⟩
  refine ⟨H, ?_, ?_⟩
  · exact (continuous_typeTwoTagName _).comp (LambdaContinuousCode.continuous_parameter r)
  · intro p
    exact functionNameValue_eq δX δY (H p) _ (hs p)

theorem hasContinuousRealizer_of_computable {δX : Representation X} {δY : Representation Y}
    {f : X → Y} (h : HasComputableRealizer δX δY f) : HasContinuousRealizer δX δY f := by
  obtain ⟨F,hF,hf⟩ := h
  exact ⟨F,hF.continuous,hf⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Continuous-realizer exponential law
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, a continuous realizer of $h$ can be paired with the unchanged argument name and followed by the fixed evaluation realizer. Pairing and composition preserve continuity on the specified name domains, and the evaluator is continuous by finite use. The composite realizes $g$ by the stated pointwise identity. Finally, any two possible maps $h$ have the same values at every parameter and argument, so extensionality gives their equality. Thus currying and evaluation are inverse for continuous realizers as well.
-/
theorem continuous_uncurry {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {h : Z → ContinuouslyRealizableMap δX δY}
    (hh : HasContinuousRealizer δZ (typeTwoFunctionRepresentation δX δY) h) :
    HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY
      (fun z => (h z.1).val z.2) := by
  have hfst := hasContinuousRealizer_of_computable (hasComputableRealizer_fst δZ δX)
  have hsnd := hasContinuousRealizer_of_computable (hasComputableRealizer_snd δZ δX)
  have hp := (continuous_realizer_product_iff _ (typeTwoFunctionRepresentation δX δY) δX
    (fun z : Z × X => (h z.1, z.2))).mpr ⟨hh.comp hfst, hsnd⟩
  exact (hasContinuousRealizer_of_computable (computable_evaluation δX δY)).comp hp

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Continuous-realizer exponential law
-/
theorem continuous_exponential_iff (δZ : Representation Z) (δX : Representation X)
    (δY : Representation Y) (g : Z × X → Y) :
    HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY g ↔
      ∃ h : Z → ContinuouslyRealizableMap δX δY,
        (∀ z x, (h z).val x = g (z, x)) ∧
        HasContinuousRealizer δZ (typeTwoFunctionRepresentation δX δY) h := by
  constructor
  · intro hg
    exact ⟨continuousCurryMap hg, fun _ _ => rfl, continuous_curry hg⟩
  · rintro ⟨h, he, hh⟩
    have hfun : (fun z : Z × X => (h z.1).val z.2) = g := funext fun z => he z.1 z.2
    rw [← hfun]
    exact continuous_uncurry hh

/-- A section map satisfying the exponential identity is unique as a represented map. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Continuous-realizer exponential law
-/
theorem continuous_exponential_exists_unique (δZ : Representation Z) (δX : Representation X)
    (δY : Representation Y) (g : Z × X → Y)
    (hg : HasContinuousRealizer (typeTwoProductRepresentation δZ δX) δY g) :
    ∃! h : Z → ContinuouslyRealizableMap δX δY,
      (∀ z x, (h z).val x = g (z, x)) ∧
      HasContinuousRealizer δZ (typeTwoFunctionRepresentation δX δY) h := by
  obtain ⟨h, he, hh⟩ := (continuous_exponential_iff δZ δX δY g).mp hg
  refine ⟨h, ⟨he, hh⟩, ?_⟩
  intro k hk
  exact curry_unique (fun z x => (hk.1 z x).trans (he z x).symm)

end LambdaFunction
end PolishSpaceBook
