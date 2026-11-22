module

public import PolishSpaceBook.RepresentedContinuousMaps
public import PolishSpaceBook.LambdaContinuousCoding
public import PolishSpaceBook.LambdaUniformInterpreter
public import PolishSpaceBook.LambdaCoproducts

@[expose] public section

/-! # Function names evaluated by closed lambda terms

The domain includes arbitrary infinite parameters and all continuous realizers.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaFunction
set_option maxRecDepth 4096
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For represented spaces $\mathbf X$ and $\mathbf Y$, let the \termdefine{represented function space}
    $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ consist of all maps $f:X\to Y$ that have a continuous realizer. A
    function name has the form $a=e\concat r$: its first entry is the syntax index of a closed lambda program $P_e$, and its
    tail is an arbitrary auxiliary name. On an input name $p$, the program uses the joined name $\langle r,p\rangle$ to
    compute the output coordinates.
    The program enumeration is the one used by the universal lambda interpreter in §{sec:lambda-program-specialization}.
-/
def functionNameProgram (a : ℕ → ℕ) : AlphaTerm :=
  Term.closedProgram (a 0)

/-- Extensional correctness of a program and its retained infinite parameter. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Such a name is valid if every $p\in\DomainOf{\delta_X}$ produces an entire name $q_p\in\DomainOf{\delta_Y}$, and $\delta_Y(q_p)$ depends only on $\delta_X(p)$. The latter condition is extensionality: different names of the same input must give the same output point, although the output names themselves may differ. Neither condition is required to be decidable. Define the value of a valid function name by $f(\delta_X(p))=\delta_Y(q_p)$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For represented spaces $\mathbf X$ and $\mathbf Y$, let the \termdefine{represented function space}
    $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ consist of all maps $f:X\to Y$ that have a continuous realizer. A
    function name has the form $a=e\concat r$: its first entry is the syntax index of a closed lambda program $P_e$, and its
    tail is an arbitrary auxiliary name. On an input name $p$, the program uses the joined name $\langle r,p\rangle$ to
    compute the output coordinates.
    The program enumeration is the one used by the universal lambda interpreter in §{sec:lambda-program-specialization}.
-/
def FunctionNameRealizes (δX : Representation X) (δY : Representation Y)
    (a : ℕ → ℕ) (f : X → Y) : Prop :=
  ∃ F : δX.domain → δY.domain,
    (∀ p n, OracleRuns (typeTwoPairName (typeTwoTailName a) p.val)
      (functionNameProgram a) n ((F p).val n)) ∧ Realizes δX δY F f

theorem FunctionNameRealizes.continuous {δX : Representation X} {δY : Representation Y}
    {a : ℕ → ℕ} {f : X → Y} (h : FunctionNameRealizes δX δY a f) :
    HasContinuousRealizer δX δY f := by
  obtain ⟨F, hc, hf⟩ := h
  exact ⟨F, LambdaContinuousCode.continuous_of_parameter _ _ hc, hf⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    A valid name determines a function because the input representation is surjective and the output is extensional. The function is unique: two proposed values agree on every represented input. Fixing the auxiliary oracle, finite use makes its name realizer continuous on the entire input-name domain. Thus the value belongs to the specified function space.
-/
theorem FunctionNameRealizes.unique {δX : Representation X} {δY : Representation Y}
    {a : ℕ → ℕ} {f g : X → Y} (hf : FunctionNameRealizes δX δY a f)
    (hg : FunctionNameRealizes δX δY a g) : f = g := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  funext x
  obtain ⟨p, rfl⟩ := δX.surjective x
  have he : F p = G p := by
    apply Subtype.ext
    funext n
    exact (hF p n).output_unique (hG p n)
  rw [← hf p, ← hg p, he]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, choose a continuous realizer of any member of the function space. The oracle-coding theorem supplies an auxiliary oracle and a finite program which computes this realizer on all valid input names. Prefix the program index to that oracle. This is a valid function name with the required value, proving surjectivity without restricting the function space to computable maps.
-/
theorem HasContinuousRealizer.exists_functionName {δX : Representation X}
    {δY : Representation Y} {f : X → Y} (h : HasContinuousRealizer δX δY f) :
    ∃ a, FunctionNameRealizes δX δY a f := by
  obtain ⟨F, hF, hf⟩ := h
  obtain ⟨r, c, hclosed, hc⟩ := (LambdaContinuousCode.continuous_iff_exists_parameter (fun p => (F p).val)).mp hF
  obtain ⟨e, he⟩ := Term.closedProgram_surjective c hclosed
  refine ⟨typeTwoTagName e r, F, ?_, hf⟩
  intro p n
  simpa only [typeTwoTail_tag, functionNameProgram, typeTwoTagName, he] using hc p n

def functionNameDomain (δX : Representation X) (δY : Representation Y) : Set (ℕ → ℕ) :=
  {a | ∃ f : ContinuouslyRealizableMap δX δY, FunctionNameRealizes δX δY a f.val}

noncomputable def functionNameValue (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) : ContinuouslyRealizableMap δX δY := a.property.choose

theorem functionNameValue_spec (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) :
    FunctionNameRealizes δX δY a.val (functionNameValue δX δY a).val := a.property.choose_spec

theorem functionNameValue_eq (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) (f : ContinuouslyRealizableMap δX δY)
    (hf : FunctionNameRealizes δX δY a.val f.val) : functionNameValue δX δY a = f := by
  apply Subtype.ext
  exact (functionNameValue_spec δX δY a).unique hf

/-- The underlying set contains every continuously realizable map. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Function-space representation
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For represented spaces $\mathbf X$ and $\mathbf Y$, let the \termdefine{represented function space}
    $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ consist of all maps $f:X\to Y$ that have a continuous realizer. A
    function name has the form $a=e\concat r$: its first entry is the syntax index of a closed lambda program $P_e$, and its
    tail is an arbitrary auxiliary name. On an input name $p$, the program uses the joined name $\langle r,p\rangle$ to
    compute the output coordinates.
    The program enumeration is the one used by the universal lambda interpreter in §{sec:lambda-program-specialization}.
-/
noncomputable def typeTwoFunctionRepresentation (δX : Representation X) (δY : Representation Y) :
    Representation (ContinuouslyRealizableMap δX δY) where
  domain := functionNameDomain δX δY
  toFun := functionNameValue δX δY
  surjective := by
    intro f
    obtain ⟨a, ha⟩ := HasContinuousRealizer.exists_functionName f.property
    exact ⟨⟨a, ⟨f, ha⟩⟩, functionNameValue_eq δX δY _ f ha⟩


/-- The simulated name consists of the function's tail and the argument name. -/
def evaluationOracle (w : ℕ → ℕ) : ℕ → ℕ :=
  typeTwoPairName (typeTwoTailName (typeTwoLeftName w)) (typeTwoRightName w)

def leftProgram : AlphaTerm := projectOutputProgram true identityProgram
def rightProgram : AlphaTerm := projectOutputProgram false identityProgram

theorem leftProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes leftProgram (fun p : D => typeTwoLeftName p.val) :=
  (identityProgram_computes D).left

theorem rightProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes rightProgram (fun p : D => typeTwoRightName p.val) :=
  (identityProgram_computes D).right

def evaluationOracleProgram : AlphaTerm :=
  pairOutputProgram (compositionProgram tailProgram leftProgram) rightProgram

theorem evaluationOracleProgram_computes :
    TypeTwoComputes evaluationOracleProgram (fun p : (Set.univ : Set (ℕ → ℕ)) => evaluationOracle p.val) := by
  have ht : TypeTwoComputes tailProgram
      (fun p : (Set.univ : Set (ℕ → ℕ)) => typeTwoTailName p.val) :=
    typeTwoComputes_iff_runs.mpr ⟨tailProgram_closed, fun p n => tailProgram_runs p.val n⟩
  let D : Set (ℕ → ℕ) := Set.univ
  let F : D → D :=
    fun p => ⟨typeTwoLeftName p.val, Set.mem_univ _⟩
  exact (ht.comp (F := F) (leftProgram_computes Set.univ)).pair (rightProgram_computes Set.univ)

def evaluationBody (O N : AlphaTerm) : AlphaTerm :=
  app (app uniformInterpreterProgram (app evaluationOracleProgram O))
    (app (app numericalPairTerm (app (app leftProgram O) (numeral 0))) N)

theorem evaluationBody_fv (O N : AlphaTerm) :
    (evaluationBody O N).fv = O.fv ∪ N.fv := by
  simp only [evaluationBody, fv_app]
  rw [uniformInterpreterProgram_closed, evaluationOracleProgram_computes.1,
    (leftProgram_computes Set.univ).1, numericalPairTerm_closed, numeral_closed]
  simp only [Finset.empty_union, Finset.union_empty, ← Finset.union_assoc, Finset.union_self]

theorem evaluationBody_subst (O N R : AlphaTerm) (x : ℕ) :
    (evaluationBody O N).subst x R = evaluationBody (O.subst x R) (N.subst x R) := by
  simp only [evaluationBody, subst_app, subst_closed _ _ _ uniformInterpreterProgram_closed,
    subst_closed _ _ _ evaluationOracleProgram_computes.1,
    subst_closed _ _ _ (leftProgram_computes Set.univ).1,
    subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ (numeral_closed 0)]

/-- One evaluator, fixed before the name, argument and output coordinate are supplied. -/
def evaluationProgram : AlphaTerm := lam 40 (lam 41 (evaluationBody (var 40) (var 41)))

theorem evaluationProgram_closed : evaluationProgram.Closed := by
  unfold evaluationProgram Closed
  simp only [fv_lam, evaluationBody_fv, fv_var]
  decide

theorem evaluationProgram_start (n : ℕ) :
    Relation.ReflTransGen Beta (app (app evaluationProgram (var 0)) (numeral n))
      (evaluationBody (var 0) (numeral n)) := by
  have h₁ : Beta (app evaluationProgram (var 0)) (lam 41 (evaluationBody (var 0) (var 41))) := by
    have he : (lam 41 (evaluationBody (var 40) (var 41))).subst 40 (var 0) =
        lam 41 (evaluationBody (var 0) (var 41)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by simp [fv_var]), evaluationBody_subst]
      simp only [subst_var, ite_true, show (41 = 40) = False by decide, ite_false]
    unfold evaluationProgram
    rw [← he]
    exact Beta.contract 40 (lam 41 (evaluationBody (var 40) (var 41))) (var 0)
  have h₂ : Beta (app (lam 41 (evaluationBody (var 0) (var 41))) (numeral n))
      (evaluationBody (var 0) (numeral n)) := by
    have he : (evaluationBody (var 0) (var 41)).subst 41 (numeral n) =
        evaluationBody (var 0) (numeral n) := by
      rw [evaluationBody_subst]
      simp only [subst_var, ite_true, show (0 = 41) = False by decide, ite_false]
    rw [← he]
    exact Beta.contract 41 (evaluationBody (var 0) (var 41)) (numeral n)
  exact .tail (.single (.app_left _ h₁)) h₂

/-- Every indexed output is simulated by substituting the computed joined name. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Use the already constructed closed terms
    $$\begin{aligned}
    I&:=\lambdaab{o}{o},\qquad
    L:=\LambdaProjectOutput{1}{I},\qquad R:=\LambdaProjectOutput{2}{I},\\
    T&:=\LambdaPairOutputs{C_{\LambdaNameTail,L}}{R}.
    \end{aligned}$$
    For $w=\langle a,p\rangle$, the program $T$ produces $\langle\NameTail{a},p\rangle$. Define the fixed evaluator by
    $$E:=\lambdaab{o}{\lambdaab{n}{
    \LambdaUniformInterpreter\,(To)\,
    \bigl(\LambdaNumericPair\,(Lo\ChurchNumeral{0})\,n\bigr)}}.$$
    All component terms are closed, so $E$ is closed. Two beta steps expose its body. The term $Lo\ChurchNumeral{0}$ returns
    $a(0)=e$, and numerical pairing supplies the input $\ChurchNumeral{\NatPair{e}{n}}$ to the universal interpreter. Each
    digit requested from $To$ is computed by the tail, projection and pairing routines. The input-substitution lemma
    therefore carries any output of $P_e$ with name $\langle\NameTail{a},p\rangle$ into an output of $E$ with name $w$. This
    is the same finite lambda term for every function name, argument name, and coordinate; it need not construct either
    infinite component in advance.
-/
theorem evaluationProgram_runs {w : ℕ → ℕ} {n m : ℕ}
    (h : OracleRuns (evaluationOracle w) (functionNameProgram (typeTwoLeftName w)) n m) :
    OracleRuns w evaluationProgram n m := by
  apply (beta_steps_oracle (evaluationProgram_start n)).trans
  have hl := (typeTwoComputes_iff_runs.mp (leftProgram_computes Set.univ)).2
    ⟨w, Set.mem_univ _⟩ 0
  have hi := (oracle_steps_app_left (oracle_steps_app_right numericalPairTerm hl) (numeral n)).trans
    (beta_steps_oracle (numericalPairTerm_apply (typeTwoLeftName w 0) n))
  apply (oracle_steps_app_right _ hi).trans
  have hu := (uniformInterpreterProgram_runs_iff (evaluationOracle w) (typeTwoLeftName w 0) n m).mpr h
  have hs := oracle_steps_subst_input (R := app evaluationOracleProgram (var 0)) hu
    (fun k => (typeTwoComputes_iff_runs.mp evaluationOracleProgram_computes).2
      ⟨w, Set.mem_univ _⟩ k)
  simpa only [subst_app, subst_var, ite_true,
    subst_closed _ _ _ uniformInterpreterProgram_closed, subst_closed _ _ _ (numeral_closed _)] using hs

noncomputable def functionNameRealizer (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) : δX.domain → δY.domain :=
  (functionNameValue_spec δX δY a).choose

theorem functionNameRealizer_runs (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) (p : δX.domain) (n : ℕ) :
    OracleRuns (typeTwoPairName (typeTwoTailName a.val) p.val) (functionNameProgram a.val) n
      ((functionNameRealizer δX δY a p).val n) :=
  (functionNameValue_spec δX δY a).choose_spec.1 p n

theorem functionNameRealizer_realizes (δX : Representation X) (δY : Representation Y)
    (a : functionNameDomain δX δY) :
    Realizes δX δY (functionNameRealizer δX δY a) (functionNameValue δX δY a).val :=
  (functionNameValue_spec δX δY a).choose_spec.2

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Computable evaluation
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For a valid function name and a valid argument name, every such coordinate computation terminates and the resulting
    sequence is a valid output name. By the defining extensionality condition, its represented value is the named function
    applied to the named argument. This proves computability of evaluation; it never requires a test for whether a function
    name is valid.
-/
theorem computable_evaluation (δX : Representation X) (δY : Representation Y) :
    HasComputableRealizer
      (typeTwoProductRepresentation (typeTwoFunctionRepresentation δX δY) δX) δY
      (fun z => z.1.val z.2) := by
  let H : (typeTwoProductRepresentation (typeTwoFunctionRepresentation δX δY) δX).domain →
      δY.domain := fun w => functionNameRealizer δX δY
        ⟨typeTwoLeftName w.val, w.property.1⟩ ⟨typeTwoRightName w.val, w.property.2⟩
  refine ⟨H, ⟨evaluationProgram, typeTwoComputes_iff_runs.mpr ⟨evaluationProgram_closed, ?_⟩⟩, ?_⟩
  · intro w n
    exact evaluationProgram_runs (functionNameRealizer_runs δX δY
      ⟨typeTwoLeftName w.val, w.property.1⟩ ⟨typeTwoRightName w.val, w.property.2⟩ n)
  · intro w
    exact functionNameRealizer_realizes δX δY _ _

/-- The original product realizer reads the retained parameter and the argument. -/
theorem functionNameRealizes_section {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    {G : (typeTwoProductRepresentation δZ δX).domain → δY.domain} {e : ℕ}
    (hc : TypeTwoComputes (Term.closedProgram e) (fun p => (G p).val))
    (hg : Realizes (typeTwoProductRepresentation δZ δX) δY G g) (p : δZ.domain) :
    FunctionNameRealizes δX δY (typeTwoTagName e p.val) (fun x => g (δZ.toFun p, x)) := by
  let F : δX.domain → δY.domain := fun q =>
    G ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩
  refine ⟨F, ?_, ?_⟩
  · intro q n
    simpa only [typeTwoTail_tag, functionNameProgram, typeTwoTagName] using
      (typeTwoComputes_iff_runs.mp hc).2
        ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩ n
  · intro q
    simpa only [F, typeTwoProductRepresentation, typeTwoLeft_pair, typeTwoRight_pair] using
      hg ⟨typeTwoPairName p.val q.val, by simp [typeTwoProductRepresentation]⟩

theorem continuous_section {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasComputableRealizer (typeTwoProductRepresentation δZ δX) δY g) (z : Z) :
    HasContinuousRealizer δX δY (fun x => g (z, x)) := by
  obtain ⟨G, ⟨P, hc⟩, hG⟩ := hg
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hc.1
  obtain ⟨p, rfl⟩ := δZ.surjective z
  rw [← he] at hc
  exact (functionNameRealizes_section hc hG p).continuous

def curryMap {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasComputableRealizer (typeTwoProductRepresentation δZ δX) δY g)
    (z : Z) : ContinuouslyRealizableMap δX δY :=
  ⟨fun x => g (z, x), continuous_section hg z⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Computable exponential law
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The program producing the function name is exactly $\LambdaNamePrefix{e}$, whose beta/query reductions were proved above. It outputs the fixed index at coordinate zero and copies one input digit at each later coordinate. The header is the original realizer index; the infinite parameter remains in the tail. Constructing this prefixing term from the original code uses only the numeral-code construction and fixed syntax constructors, so it is primitive recursive.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Let a finite program with index $e$ realize $g$. Given a name $p$ of $z$, output $e\concat p$. On an argument name, this
    function name runs the original program with the paired names as its oracle, so it realizes the section at $z$. The
    section realizer is continuous by finite use with $p$ fixed as its auxiliary oracle. Different names of $z$ give the
    same represented section because the original program realizes $g$.
-/
theorem computable_curry {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {g : Z × X → Y}
    (hg : HasComputableRealizer (typeTwoProductRepresentation δZ δX) δY g) :
    HasComputableRealizer δZ (typeTwoFunctionRepresentation δX δY) (curryMap hg) := by
  obtain ⟨G, ⟨P, hc⟩, hG⟩ := hg
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hc.1
  have hcode : TypeTwoComputes (Term.closedProgram e) (fun p => (G p).val) := he ▸ hc
  have hs (p : δZ.domain) := functionNameRealizes_section hcode hG p
  let H : δZ.domain → (typeTwoFunctionRepresentation δX δY).domain := fun p =>
    ⟨typeTwoTagName e p.val, ⟨curryMap ⟨G, ⟨P, hc⟩, hG⟩ (δZ.toFun p), hs p⟩⟩
  refine ⟨H, ⟨tagProgram e, typeTwoComputes_iff_runs.mpr
    ⟨tagProgram_closed e, fun p n => tagProgram_runs p.val e n⟩⟩, ?_⟩
  intro p
  exact functionNameValue_eq δX δY (H p) _ (hs p)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Computable exponential law
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let $Q$ realize a map into the function space. With $L,R,E$ as in the evaluation proof, form
    $$C_{E,\LambdaPairOutputs{C_{Q,L}}{R}}.$$
    On a paired input name, $C_{Q,L}$ computes the function name from the first component, and $R$ reads the second component. Pair their outputs and apply the fixed evaluator. Input substitution produces each requested intermediate digit when needed. This is an explicit finite lambda term, and inserting the supplied closed term $Q$ into this fixed expression is primitive recursive on syntax codes. Evaluation after currying returns the original map on every pair of points. In the other direction, every resulting section agrees pointwise with the original function-space value, so extensionality gives equality of the curried maps.
-/
theorem computable_uncurry {δZ : Representation Z} {δX : Representation X}
    {δY : Representation Y} {h : Z → ContinuouslyRealizableMap δX δY}
    (hh : HasComputableRealizer δZ (typeTwoFunctionRepresentation δX δY) h) :
    HasComputableRealizer (typeTwoProductRepresentation δZ δX) δY
      (fun z => (h z.1).val z.2) := by
  have hp := (hasComputableRealizer_product_iff _ (typeTwoFunctionRepresentation δX δY) δX
    (fun z : Z × X => (h z.1, z.2))).mpr
      ⟨hh.comp (hasComputableRealizer_fst δZ δX), hasComputableRealizer_snd δZ δX⟩
  exact (computable_evaluation δX δY).comp hp

theorem computable_exponential_iff (δZ : Representation Z) (δX : Representation X)
    (δY : Representation Y) (g : Z × X → Y) :
    HasComputableRealizer (typeTwoProductRepresentation δZ δX) δY g ↔
      ∃ h : Z → ContinuouslyRealizableMap δX δY,
        (∀ z x, (h z).val x = g (z, x)) ∧
        HasComputableRealizer δZ (typeTwoFunctionRepresentation δX δY) h := by
  constructor
  · intro hg
    exact ⟨curryMap hg, fun _ _ => rfl, computable_curry hg⟩
  · rintro ⟨h, he, hh⟩
    have hfun : (fun z : Z × X => (h z.1).val z.2) = g := funext fun z => he z.1 z.2
    rw [← hfun]
    exact computable_uncurry hh

theorem curry_unique {δX : Representation X} {δY : Representation Y}
    {h k : Z → ContinuouslyRealizableMap δX δY}
    (he : ∀ z x, (h z).val x = (k z).val x) : h = k := by
  funext z
  exact Subtype.ext (funext (he z))

/-- A name is computable by one closed, oracle-free numerical lambda term. -/
def ComputableName (a : ℕ → ℕ) : Prop :=
  ∃ A : AlphaTerm, A.Closed ∧ ∀ n,
    Relation.ReflTransGen Beta (app A (numeral n)) (numeral (a n))

/-- Closed reductions cannot contain an input query. -/
theorem beta_steps_of_closed {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) (hc : M.Closed) :
    Relation.ReflTransGen Beta M N := by
  induction h with
  | refl => exact .refl
  | @tail N K hs ht ih =>
    have hn : N.Closed := Finset.eq_empty_iff_forall_notMem.mpr
      (fun x hx => by
        have hmem := oracle_steps_fv_subset hs hx
        rw [hc] at hmem
        exact Finset.notMem_empty x hmem)
    exact ih.tail (ht.beta_of_closed hn)

/-- Uniform computation of a fixed name is equivalent to oracle-free computation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Here a name $a$ is computable when one closed lambda term $A$ satisfies
    $A\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{a(n)}$ for every $n$. Equivalently, one closed Type-Two program produces
    $a$ independently of the supplied input name. In one direction, use $\lambdaab{o}{A}$. In the other direction, supply
    the constant-zero name by the closed term $\lambdaab{k}{\ChurchNumeral{0}}$. Input substitution preserves every required
    output, and the resulting computation starts from a closed term. No query step is possible from a closed term, and
    reduction preserves closedness, so the entire computation consists of beta steps.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Computability strictly refines continuity, but the
    refinement has two parts. A realizer must eventually find enough input to determine the $n$-th output coordinate, and it
    must also compute the value of that coordinate. A continuous function with a computable modulus need not be computable:
    the constant map $p\mapsto c$ has the trivial modulus for every $c\in\BaireSpace$, but it is computable only when the
    point $c$ is \termforwardas{computable point}{computable}.
-/
theorem computableName_iff_constant (a : ℕ → ℕ) :
    ComputableName a ↔ TypeTwoComputable (fun _ : (Set.univ : Set (ℕ → ℕ)) => a) := by
  constructor
  · rintro ⟨A,hA,h⟩
    let P := lam 40 A
    have hP : P.Closed := by change (lam 40 A).fv = ∅; rw [fv_lam,hA]; rfl
    refine ⟨P, typeTwoComputes_iff_runs.mpr ⟨hP, fun p n => ?_⟩⟩
    have hb : Beta (app P (var 0)) A := by
      simpa only [subst_closed _ _ _ hA] using Beta.contract 40 A (var 0)
    exact (beta_steps_oracle (.single (.app_left _ hb))).trans (beta_steps_oracle (h n))
  · rintro ⟨P,hP⟩
    let O := lam 40 (numeral 0)
    have hO : O.Closed := by change (lam 40 (numeral 0)).fv = ∅; rw [fv_lam,numeral_closed]; rfl
    have ho (n : ℕ) : Relation.ReflTransGen (OracleStep (fun _ => 0))
        (app O (numeral n)) (numeral 0) := by
      apply beta_steps_oracle
      apply Relation.ReflTransGen.single
      simpa only [subst_closed _ _ _ (numeral_closed 0)] using
        (Beta.contract 40 (numeral 0) (numeral n))
    have hc : (app P O).Closed := by unfold Closed; rw [fv_app,hP.1,hO]; rfl
    refine ⟨app P O, hc, fun n => ?_⟩
    have hs := oracle_steps_subst_input
      ((typeTwoComputes_iff_runs.mp hP).2 ⟨fun _ => 0, Set.mem_univ _⟩ n) ho
    have he : Relation.ReflTransGen (OracleStep (fun _ => 0))
        (app (app P O) (numeral n)) (numeral (a n)) := by
      simpa only [subst_app, subst_var, ite_true, subst_closed _ _ _ hP.1,
        subst_closed _ _ _ (numeral_closed _)] using hs
    apply beta_steps_of_closed he
    unfold Closed
    rw [fv_app,hc,numeral_closed]; rfl

/-- A computable retained name is supplied by its closed lambda name producer. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    If the function name $a$ is computable, let $B$ be a closed program producing it independently of its input. Put $I:=\lambdaab{o}{o}$ and
    $$S:=\LambdaPairOutputs{C_{\LambdaNameTail,B}}{I}.$$
    On input $p$, this program produces $\langle\NameTail{a},p\rangle$. Hence $C_{P_{a(0)},S}$ realizes the named function, by input substitution. Conversely, let $P$ be a computable realizer and put $R:=\LambdaProjectOutput{2}{I}$. The closed program $C_{P,R}$ ignores the auxiliary component of a joined name and runs $P$ on its input component. Choose its syntax index $e$. Then $e\concat r_0$, where $r_0(n)=0$ for every $n$, is a computable function name for the original map: prefix the fixed index to the constant-zero name.
-/
theorem FunctionNameRealizes.computable {δX : Representation X} {δY : Representation Y}
    {a : ℕ → ℕ} {f : X → Y} (hf : FunctionNameRealizes δX δY a f)
    (ha : ComputableName a) : HasComputableRealizer δX δY f := by
  obtain ⟨F,hF,hf⟩ := hf
  obtain ⟨A,hA⟩ := (computableName_iff_constant a).mp ha
  have ht : TypeTwoComputes tailProgram
      (fun p : (Set.univ : Set (ℕ → ℕ)) => typeTwoTailName p.val) :=
    typeTwoComputes_iff_runs.mpr ⟨tailProgram_closed, fun p n => tailProgram_runs p.val n⟩
  let D : Set (ℕ → ℕ) := Set.univ
  let C : D → D := fun _ => ⟨a, Set.mem_univ _⟩
  have hr := (ht.comp (F := C) hA).pair (identityProgram_computes Set.univ)
  let R := pairOutputProgram (compositionProgram tailProgram A) identityProgram
  refine ⟨F, ⟨compositionProgram (functionNameProgram a) R,
    typeTwoComputes_iff_runs.mpr ⟨compositionProgram_closed (Term.closedProgram_closed _) hr.1, ?_⟩⟩, hf⟩
  intro p n
  exact compositionProgram_runs (Term.closedProgram_closed _) hr.1 (hF p n)
    (fun k => (typeTwoComputes_iff_runs.mp hr).2 ⟨p.val, Set.mem_univ _⟩ k)

theorem exists_computable_functionName {δX : Representation X} {δY : Representation Y}
    {f : X → Y} (hf : HasComputableRealizer δX δY f) :
    ∃ a, ComputableName a ∧ FunctionNameRealizes δX δY a f := by
  obtain ⟨F,⟨P,hP⟩,hf⟩ := hf
  let Q := compositionProgram P rightProgram
  have hQ := compositionProgram_closed hP.1 (rightProgram_computes Set.univ).1
  obtain ⟨e,he⟩ := Term.closedProgram_surjective Q hQ
  let a := typeTwoTagName e (fun _ => 0)
  refine ⟨a, ?_, F, ?_, hf⟩
  · apply (computableName_iff_constant a).mpr
    have ht : TypeTwoComputes (tagProgram e)
        (fun p : (Set.univ : Set (ℕ → ℕ)) => typeTwoTagName e p.val) :=
      typeTwoComputes_iff_runs.mpr ⟨tagProgram_closed e, fun p n => tagProgram_runs p.val e n⟩
    let D : Set (ℕ → ℕ) := Set.univ
    let C : D → D :=
      fun _ => ⟨fun _ => 0, Set.mem_univ _⟩
    exact ⟨_, ht.comp (F := C) (constantProgram_computes Set.univ 0)⟩
  · intro p n
    change OracleRuns (typeTwoPairName (typeTwoTailName a) p.val)
      (Term.closedProgram e) n ((F p).val n)
    rw [he]
    apply compositionProgram_runs hP.1 (rightProgram_computes Set.univ).1
      ((typeTwoComputes_iff_runs.mp hP).2 p n)
    intro k
    simpa only [typeTwoRight_pair] using
      (typeTwoComputes_iff_runs.mp (rightProgram_computes Set.univ)).2
        ⟨typeTwoPairName (typeTwoTailName a) p.val, Set.mem_univ _⟩ k

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Function-space representation
-/
theorem computable_functionName_iff (δX : Representation X) (δY : Representation Y) (f : X → Y) :
    (∃ a, ComputableName a ∧ FunctionNameRealizes δX δY a f) ↔ HasComputableRealizer δX δY f :=
  ⟨fun ⟨_,ha,hf⟩ => hf.computable ha, exists_computable_functionName⟩

/-- Computable points of the constructed representation are precisely computable maps. -/
theorem representation_computable_name_iff (δX : Representation X) (δY : Representation Y)
    (f : ContinuouslyRealizableMap δX δY) :
    (∃ a : (typeTwoFunctionRepresentation δX δY).domain,
      ComputableName a.val ∧ (typeTwoFunctionRepresentation δX δY).toFun a = f) ↔
      HasComputableRealizer δX δY f.val := by
  constructor
  · rintro ⟨a,ha,hf⟩
    have hn := functionNameValue_spec δX δY a
    change functionNameValue δX δY a = f at hf
    rw [hf] at hn
    exact hn.computable ha
  · intro hf
    obtain ⟨a,ha,hn⟩ := exists_computable_functionName hf
    exact ⟨⟨a,⟨f,hn⟩⟩,ha,functionNameValue_eq δX δY _ f hn⟩

end LambdaFunction
end PolishSpaceBook
