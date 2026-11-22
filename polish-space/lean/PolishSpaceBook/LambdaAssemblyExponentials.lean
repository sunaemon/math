module

public import PolishSpaceBook.LambdaAssemblyProducts
public import PolishSpaceBook.LambdaFunctionSpaces

@[expose] public section

/-! # Function objects of assemblies and restriction of TTE functions

A function realizer is a uniform numerical tracker. The comparison from TTE
function names is built from evaluation and parameter abstraction.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
universe u

namespace Assembly

/-- The carrier consists of tracked functions; realizers are their tracking indices. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Function objects of assemblies
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Products organize the input to a binary operation, while function objects organize the input to an operation on
    functions. The following constructions make both kinds of evidence explicit before they are used in internal analysis.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    A procedure selecting a zero takes a function as input. We therefore specify the evidence that represents a
    function before comparing name-based computation with internal analysis. Write $\mathsf{Asm}$ for the category
    of assemblies defined above.
-/
def exponential (A B : Assembly.{u}) : Assembly.{u} where
  Carrier := Hom A B
  realizes f := uniformImp A.realizes (fun x => B.realizes (f.toFun x))
  inhabited f := by
    obtain ⟨e,he⟩ := (reduces_iff _ _).mp f.tracked
    exact ⟨e,he⟩

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Every assembly morphism has a tracker, so every element of the proposed function object has a realizer.
    For evaluation, an input realizer has the form $\NatPair{e}{a}$ with $e\in E_{\funcspace{A}{B}}(f)$ and
    $a\in E_A(x)$. The closed term
    $$V:=\lambdaab{z}{U(\LambdaNumericProjection{1}z)(\LambdaNumericProjection{2}z)},\qquad
    U:=\LambdaOutputSearch,$$
    returns a member of $E_B(f(x))$. The two projections terminate, and the tracking condition on $e$ supplies the
    terminating universal evaluation. The same program works for all $f,x$.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    A procedure selecting a zero takes a function as input. We therefore specify the evidence that represents a
    function before comparing name-based computation with internal analysis. Write $\mathsf{Asm}$ for the category
    of assemblies defined above.
-/
def evaluation (A B : Assembly.{u}) : Hom (prod (exponential A B) A) B where
  toFun p := p.1.toFun p.2
  tracked := by
    exact uniformImp_apply (φ := fun _ => A.realizes)
      (ψ := fun (p : Hom A B × A.Carrier) x => B.realizes (p.1.toFun x))
      (reduces_and_left _ _) Prod.snd (reduces_and_right _ _)

/-- The index factory is total even on numbers which realize no parameter. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Let $h:C\times A\to B$ have tracker $d$. For a realizer $a$ of $z\in|C|$, construct
    $$c(d,a):=\LambdaSyntaxCode{\lambdaab{b}{U\ChurchNumeral{d}(\LambdaNumericPair\,\ChurchNumeral{a}\,b)}}.$$
    The code factory in §{sec:effective-topos-construction} computes this number on every input $a$, without evaluating
    $h$. On an argument realizer $b\in E_A(x)$, the resulting program has exactly the outputs of
    $d\cdot\NatPair{a}{b}$, so it returns a member of $E_B(h(z,x))$. Hence each section $x\mapsto h(z,x)$ is an
    assembly morphism, and the total code factory tracks
    $$\widehat h:C\longrightarrow\funcspace{A}{B},\qquad \widehat h(z)(x)=h(z,x).$$
    The chosen underlying point $z$ is never an input to this factory; only its numerical realizer $a$ is supplied.
-/
theorem curry_indices {C A B : Assembly.{u}} (f : Hom (prod C A) B) :
    ∃ t : ℕ → ℕ, (∃ k, ∀ a, App k a (t a)) ∧
      ∀ z a, a ∈ C.realizes z → ∀ x b, b ∈ A.realizes x →
        ∃ c, App (t a) b c ∧ c ∈ B.realizes (f.toFun (z,x)) := by
  obtain ⟨e,he⟩ := (reduces_iff _ _).mp f.tracked
  obtain ⟨outer,body,_,_,hout,hbody⟩ := exists_computable_curry_indices
  refine ⟨body e,⟨outer e,hout e⟩,fun z a ha x b hb => ?_⟩
  obtain ⟨c,hc,hcB⟩ := he (z,x) (Nat.pair a b) (by simpa [prod,realizabilityAnd] using And.intro ha hb)
  exact ⟨c,(hbody e a b c).mpr hc,hcB⟩

def Hom.section {C A B : Assembly.{u}} (f : Hom (prod C A) B) (z : C.Carrier) : Hom A B where
  toFun x := f.toFun (z,x)
  tracked := by
    obtain ⟨t,_,ht⟩ := curry_indices f
    obtain ⟨a,ha⟩ := C.inhabited z
    exact (reduces_iff _ _).mpr ⟨t a,ht z a ha⟩

def curry {C A B : Assembly.{u}} (f : Hom (prod C A) B) : Hom C (exponential A B) where
  toFun := f.section
  tracked := by
    obtain ⟨t,⟨k,hk⟩,ht⟩ := curry_indices f
    exact (reduces_iff _ _).mpr ⟨k,fun z a ha => ⟨t a,hk a,ht z a ha⟩⟩

def uncurry {C A B : Assembly.{u}} (f : Hom C (exponential A B)) : Hom (prod C A) B :=
  (((fst C A).comp f).pair (snd C A)).comp (evaluation A B)

@[simp] theorem uncurry_curry {C A B : Assembly.{u}} (f : Hom (prod C A) B) :
    uncurry (curry f) = f := Hom.ext (fun _ => rfl)

@[simp] theorem curry_uncurry {C A B : Assembly.{u}} (f : Hom C (exponential A B)) :
    curry (uncurry f) = f := Hom.ext (fun _ => Hom.ext (fun _ => rfl))

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Conversely, evaluate a morphism $k:C\to\funcspace{A}{B}$ after pairing it with the argument projection.
    This gives $(z,x)\mapsto k(z)(x)$. Evaluation after currying returns $h$, and currying after evaluation returns
    $k$, since assembly morphisms are determined by their underlying functions. Replacing the parameter by
    $\ell:D\to C$ gives
    $$\widehat{h\circ(\ell\times\mathrm{id}_A)}=\widehat h\circ\ell,$$
    which proves naturality. The singleton with every natural number as a realizer is terminal: the identity program
    tracks the unique underlying map into it. Thus the displayed product and function objects give the claimed
    cartesian closed structure.
-/
def curryEquiv (C A B : Assembly.{u}) : Hom (prod C A) B ≃ Hom C (exponential A B) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

theorem curry_natural {W C A B : Assembly.{u}} (k : Hom W C) (f : Hom (prod C A) B) :
    curry ((((fst W A).comp k).pair (snd W A)).comp f) = k.comp (curry f) :=
  Hom.ext (fun _ => Hom.ext (fun _ => rfl))

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Finally, suppose $B$ is modest and $e$ realizes both $f$ and $g$. For each $x\in|A|$, choose
    $a\in E_A(x)$. Numerical output uniqueness makes the outputs of $e\cdot a$ used for $f$ and $g$ equal.
    This common output realizes both $f(x)$ and $g(x)$, so modesty gives $f(x)=g(x)$. Extensionality gives $f=g$.
    \end{proof}
-/
theorem exponential_modest (A B : Assembly.{u}) (hB : B.IsModest) :
    (exponential A B).IsModest := by
  intro f g e hf hg
  apply Hom.ext
  intro x
  obtain ⟨a,ha⟩ := A.inhabited x
  obtain ⟨b,hb,hbB⟩ := hf x a ha
  obtain ⟨c,hc,hcB⟩ := hg x a ha
  have h := app_unique hb hc
  exact hB _ _ b hbB (h ▸ hcB)

open CategoryTheory Limits

def terminal : Assembly.{u} where
  Carrier := PUnit
  realizes _ := Set.univ
  inhabited _ := ⟨0,Set.mem_univ _⟩

def toTerminal (A : Assembly.{u}) : Hom A terminal :=
  ⟨fun _ => PUnit.unit,reduces_top _⟩

def terminalIsTerminal : IsTerminal terminal.{u} :=
  IsTerminal.ofUniqueHom toTerminal (fun _ _ => Hom.ext (fun _ => @Subsingleton.elim PUnit inferInstance _ _))

def productIsLimit (A B : Assembly.{u}) : IsLimit (BinaryFan.mk (C := Assembly.{u}) (fst A B) (snd A B)) :=
  BinaryFan.isLimitMk (fun s => s.fst.pair s.snd)
    (fun s => Hom.pair_fst s.fst s.snd) (fun s => Hom.pair_snd s.fst s.snd)
    (fun s m h₁ h₂ => (Hom.prod_unique m).symm.trans
      (congrArg₂ (fun (f : Hom s.pt A) (g : Hom s.pt B) => f.pair g) h₁ h₂))

/-- The categorical structure uses the same displayed products and evaluation. -/
noncomputable abbrev cartesianMonoidal : CartesianMonoidalCategory Assembly.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨asEmptyCone terminal,terminalIsTerminal⟩
    (fun A B => ⟨BinaryFan.mk (C := Assembly.{u}) (fst A B) (snd A B),productIsLimit A B⟩)

attribute [instance] cartesianMonoidal

noncomputable instance assemblyBraided : BraidedCategory Assembly.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

theorem curry_natural_tensor (A : Assembly.{u})
    (W C B : Assembly.{u}) (k : W ⟶ C) (f : prod C A ⟶ B) :
    curry ((MonoidalCategory.tensorRight A).map k ≫ f) = k ≫ curry f := by
  apply Hom.ext
  intro w
  apply Hom.ext
  intro a
  rfl

noncomputable def exponentialFunctor (A : Assembly.{u}) : Assembly.{u} ⥤ Assembly.{u} :=
  Adjunction.rightAdjointOfEquiv (F := MonoidalCategory.tensorRight A)
    (fun C B => curryEquiv C A B) (curry_natural_tensor A)

noncomputable def exponentialAdjunction (A : Assembly.{u}) :
    MonoidalCategory.tensorRight A ⊣ exponentialFunctor A :=
  Adjunction.adjunctionOfEquivRight (F := MonoidalCategory.tensorRight A)
    (fun C B => curryEquiv C A B) (curry_natural_tensor A)

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Function objects of assemblies
-/
noncomputable instance assemblyMonoidalClosed : MonoidalClosed Assembly.{u} where
  closed A := {
    rightAdj := exponentialFunctor A
    adj := (exponentialAdjunction A).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight A).symm }

end Assembly

variable {X Y : Type u} (δX : Representation X) (δY : Representation Y)

/-- Evaluation on computable points uses pairing of indices and then the TTE evaluator. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The computable TTE evaluator and the computable-point product isomorphism give an assembly morphism
    $$H:F\times A_{\delta_X}\longrightarrow A_{\delta_Y},\qquad H(f,x)=f(x).$$
    In detail, the pairing-index map $s$ from §{sec:effective-topos-products-addition} combines a function-name index
    and an argument-name index. Apply the name-to-index compiler for the fixed TTE evaluation program to $s$'s
    output. The composite is total on numerical inputs and tracks $H$ on valid realizers. Fix one index $d$ for
    this composite. Currying $H$ gives $J$, and
    $$t(e):=c(d,e)$$
    is the total compiler in the statement. For every $a\in E_{A_{\delta_X}}(x)$, its defining reduction gives
    $$t(e)\cdot a\simeq d\cdot\NatPair{e}{a}\in E_{A_{\delta_Y}}(f(x)).$$
    The underlying section is exactly the restriction of $f$ to computable points, and the evaluation identity is the
    uncurrying identity already proved.
    \end{proof}
-/
noncomputable def computableFunctionEvaluation : Assembly.Hom
    (Assembly.prod (computablePointAssembly (LambdaFunction.typeTwoFunctionRepresentation δX δY))
      (computablePointAssembly δX)) (computablePointAssembly δY) :=
  (computablePointPair (LambdaFunction.typeTwoFunctionRepresentation δX δY) δX).comp
    (computablePointMap (LambdaFunction.computable_evaluation δX δY))

/-- This is a comparison morphism, not an asserted identification of the two function objects. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: Restriction of TTE functions
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Now let $\delta_{\mathcal C}$ be the representation of $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ from
    §{sec:tte-represented-constructions}, and put $F:=A_{\delta_{\mathcal C}}$.
    An element of $F$ is an external function with a computable function name; a realizer of this element is an
    index computing such a name. This differs from a realizer in $\funcspace{A_{\delta_X}}{A_{\delta_Y}}$, which
    acts directly on indices of computable input names.
-/
noncomputable def computableFunctionRestriction : Assembly.Hom
    (computablePointAssembly (LambdaFunction.typeTwoFunctionRepresentation δX δY))
    (Assembly.exponential (computablePointAssembly δX) (computablePointAssembly δY)) :=
  Assembly.curry (computableFunctionEvaluation δX δY)

@[simp] theorem computableFunctionRestriction_apply
    (f : (computablePointAssembly (LambdaFunction.typeTwoFunctionRepresentation δX δY)).Carrier)
    (x : (computablePointAssembly δX).Carrier) :
    (((computableFunctionRestriction δX δY).toFun f).toFun x).val = f.val.val x.val := rfl

/-- A total compiler turns a function-name index into a tracker on computable input points. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: Restriction of TTE functions
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Now let $\delta_{\mathcal C}$ be the representation of $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ from
    §{sec:tte-represented-constructions}, and put $F:=A_{\delta_{\mathcal C}}$.
    An element of $F$ is an external function with a computable function name; a realizer of this element is an
    index computing such a name. This differs from a realizer in $\funcspace{A_{\delta_X}}{A_{\delta_Y}}$, which
    acts directly on indices of computable input names.
-/
theorem computableFunctionRestriction_indices : ∃ t : ℕ → ℕ, (∃ k, ∀ e, App k e (t e)) ∧
    ∀ f e, e ∈ (computablePointAssembly (LambdaFunction.typeTwoFunctionRepresentation δX δY)).realizes f →
      t e ∈ (Assembly.exponential (computablePointAssembly δX) (computablePointAssembly δY)).realizes
        ((computableFunctionRestriction δX δY).toFun f) := by
  obtain ⟨t,ht,h⟩ := Assembly.curry_indices (computableFunctionEvaluation δX δY)
  exact ⟨t,ht,h⟩

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    For real analysis, we may now take $A:=A_{\rho_{\R}}$ and use $\funcspace{A}{A}$ as a specified function assembly.
    Its embedding is a specified object of $\EffCat$, with evaluation induced by the assembly embedding and its product
    calculation. The proposition supplies a comparison from computably named external functions to this object.
    It does not assert an inverse comparison, nor convert an arbitrary tracker into a Type-Two program on names.
    The finite-query argument in §{sec:effective-topos-zero-selection} concerns function names; the self-reference
    argument in §{sec:effective-topos-index-zero-selection} separately rules out zero selection on function trackers.
-/
@[simp] theorem computableFunctionRestriction_evaluation :
    Assembly.uncurry (computableFunctionRestriction δX δY) = computableFunctionEvaluation δX δY :=
  Assembly.uncurry_curry _

end PolishSpaceBook.LambdaIndexPCA
