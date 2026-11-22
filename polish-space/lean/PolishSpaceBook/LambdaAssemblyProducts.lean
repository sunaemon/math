module

public import PolishSpaceBook.LambdaComputablePointAssemblies
public import PolishSpaceBook.LambdaProducts

@[expose] public section

/-! # Products of assemblies and computable names

Pairing indices is a finite syntax construction. It does not run either name.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
universe u

namespace Assembly

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: Products of assemblies
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Products organize the input to a binary operation, while function objects organize the input to an operation on
    functions. The following constructions make both kinds of evidence explicit before they are used in internal analysis.
-/
def prod (A B : Assembly.{u}) : Assembly.{u} where
  Carrier := A.Carrier × B.Carrier
  realizes := realizabilityAnd (fun x => A.realizes x.1) (fun x => B.realizes x.2)
  inhabited x := by
    obtain ⟨a,ha⟩ := A.inhabited x.1
    obtain ⟨b,hb⟩ := B.inhabited x.2
    exact ⟨Nat.pair a b,by simpa [realizabilityAnd] using And.intro ha hb⟩

def fst (A B : Assembly.{u}) : Hom (prod A B) A :=
  ⟨Prod.fst,reduces_and_left _ _⟩

def snd (A B : Assembly.{u}) : Hom (prod A B) B :=
  ⟨Prod.snd,reduces_and_right _ _⟩

def Hom.pair {A B C : Assembly.{u}} (f : Hom C A) (g : Hom C B) : Hom C (prod A B) :=
  ⟨fun x => (f.toFun x,g.toFun x),reduces_and_intro f.tracked g.tracked⟩

@[simp] theorem Hom.pair_fst {A B C : Assembly.{u}} (f : Hom C A) (g : Hom C B) :
    (f.pair g).comp (fst A B) = f := Hom.ext (fun _ => rfl)

@[simp] theorem Hom.pair_snd {A B C : Assembly.{u}} (f : Hom C A) (g : Hom C B) :
    (f.pair g).comp (snd A B) = g := Hom.ext (fun _ => rfl)

theorem Hom.prod_unique {A B C : Assembly.{u}} (h : Hom C (prod A B)) :
    (h.comp (fst A B)).pair (h.comp (snd A B)) = h := Hom.ext (fun _ => rfl)

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each pair has a realizer because each coordinate does. The two numerical projections track the coordinate maps.
    If $g:C\to A$ and $h:C\to B$ have trackers $a,b$, the program
    $$\lambdaab{z}{\LambdaNumericPair\,((U\ChurchNumeral{a})z)\,((U\ChurchNumeral{b})z)}$$
    tracks $c\mapsto(g(c),h(c))$, where $U:=\LambdaOutputSearch$. Both evaluations terminate on every realizer of $c$.
    Composing with the projections recovers $g,h$. Every map with these two coordinates has this underlying
    function, so uniqueness follows from the definition of assembly morphisms.
    For the embedding, a number $z$ realizes equality between $(x,y)$ and $(x',y')$ precisely when
    $$x=x',\quad y=y',\quad
    \pi_1(z)\in E_A(x),\quad\pi_2(z)\in E_B(y).$$
    The product of the two embedded PERs has exactly the same equality realizers. The product construction in
    §{sec:effective-topos-finite-limits} therefore identifies these objects, including their projection maps.
    \end{proof}
-/
theorem prod_toPER (A B : Assembly.{u}) :
    (prod A B).toPER = RealizerPER.product A.toPER B.toPER := by
  have hr : (prod A B).toPER.rel = (RealizerPER.product A.toPER B.toPER).rel := by
    funext x y
    ext z
    simp only [toPER,prod,RealizerPER.product,realizabilityAnd,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h,ha,hb⟩
      exact ⟨⟨congrArg Prod.fst h,ha⟩,⟨congrArg Prod.snd h,hb⟩⟩
    · rintro ⟨⟨ha,he⟩,⟨hb,hf⟩⟩
      exact ⟨Prod.ext ha hb,he,hf⟩
  unfold toPER RealizerPER.product
  congr 1

end Assembly

/-- A total constructor for an index of the pointwise paired name. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: Pairing name indices
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $z=\NatPair{e}{f}$, construct the code
    $$s(z):=\LambdaSyntaxCode{\lambdaab{n}{\LambdaNumericPair\,((U\ChurchNumeral{e})n)\,((U\ChurchNumeral{f})n)}}.$$
    Fix named representatives of $U$ and numerical pairing. Numerical projections extract $e,f$ from $z$;
    numeral-code, application-code, and abstraction-code construction then produce the displayed finite syntax.
    Every stage terminates on every $z$, independently of whether either index computes a total name.
    If the two indices compute $p,q$, applying the constructed term to $\ChurchNumeral{n}$ first substitutes $n$,
    then evaluates the two names, and finally pairs their outputs. These finite beta reductions return
    $\ChurchNumeral{\NatPair{p(n)}{q(n)}}$ for every $n$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    To interpret a binary operation internally, we must relate a pair of realized points to a computable name of a
    pair. We first make this passage explicit.
-/
theorem pairName_indices : ∃ t : ℕ → ℕ, (∃ k, ∀ z, App k z (t z)) ∧
    ∀ e f p q, ComputesName e p → ComputesName f q →
      ComputesName (t (Nat.pair e f)) (typeTwoPairName p q) := by
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨U,hU⟩ := Quotient.exists_rep outputSearchTerm
  have hB' : mk B = numericalPairTerm := hB
  have hU' : mk U = outputSearchTerm := hU
  let S (z : ℕ) : Term := .lam 40
    (.app (.app B (.app (.app U (Term.churchNumeral z.unpair.1)) (.var 40)))
      (.app (.app U (Term.churchNumeral z.unpair.2)) (.var 40)))
  have hm (z : ℕ) : mk (S z) = pairNumerical (evalProgram z.unpair.1) (evalProgram z.unpair.2) := by
    change lam 40 (app (app (mk B) (app (app (mk U) (mk (Term.churchNumeral z.unpair.1))) (var 40)))
      (app (app (mk U) (mk (Term.churchNumeral z.unpair.2))) (var 40))) = _
    rw [hB',hU',Term.mk_churchNumeral,Term.mk_churchNumeral]
    rfl
  have hc (z : ℕ) : (mk (S z)).Closed := by
    rw [hm]
    unfold pairNumerical numericalCombine Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [numericalPairTerm_closed,evalProgram_closed,evalProgram_closed]
    simp
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have hl := ((numericalConstant_computes U.code).applicationCode
    (hn.comp (projection_computes true))).applicationCode (numericalConstant_computes (Term.var 40).code)
  have hr := ((numericalConstant_computes U.code).applicationCode
    (hn.comp (projection_computes false))).applicationCode (numericalConstant_computes (Term.var 40).code)
  have ht := ((numericalConstant_computes B.code).applicationCode hl).applicationCode hr |>.abstractionCode 40
  obtain ⟨k,hk⟩ := Term.closedProgram_surjective _ ht.1
  refine ⟨fun z => (S z).code,⟨k,fun z => ?_⟩,fun e f p q hp hq n => ?_⟩
  · unfold App
    rw [hk]
    exact ht.2 z
  · unfold App
    rw [closedProgram_code_of_closed _ (hc _),hm]
    simpa only [Nat.unpair_pair,typeTwoPairName] using (hp.eval.pair hq.eval).2 n

variable {X Y : Type u} (δX : Representation X) (δY : Representation Y)

theorem hasComputableName_pair {x : X} {y : Y}
    (hx : HasComputableName δX x) (hy : HasComputableName δY y) :
    HasComputableName (typeTwoProductRepresentation δX δY) (x,y) := by
  obtain ⟨p,hp,e,he⟩ := hx
  obtain ⟨q,hq,f,hf⟩ := hy
  obtain ⟨t,_,ht⟩ := pairName_indices
  refine ⟨⟨typeTwoPairName p.val q.val,by
    change typeTwoLeftName (typeTwoPairName p.val q.val) ∈ δX.domain ∧
      typeTwoRightName (typeTwoPairName p.val q.val) ∈ δY.domain
    simpa only [typeTwoLeft_pair,typeTwoRight_pair] using And.intro p.property q.property⟩,?_,t (Nat.pair e f),ht e f p.val q.val he hf⟩
  apply Prod.ext
  · simpa [typeTwoProductRepresentation] using hp
  · simpa [typeTwoProductRepresentation] using hq

/-- The map pairs semantic points, while its tracker compiles their name indices. -/
def computablePointPair : Assembly.Hom
    (Assembly.prod (computablePointAssembly δX) (computablePointAssembly δY))
    (computablePointAssembly (typeTwoProductRepresentation δX δY)) where
  toFun x := ⟨(x.1.val,x.2.val),hasComputableName_pair δX δY x.1.property x.2.property⟩
  tracked := by
    obtain ⟨t,⟨k,hk⟩,ht⟩ := pairName_indices
    apply (reduces_iff _ _).mpr
    refine ⟨k,fun x z hz => ?_⟩
    obtain ⟨p,hp,he⟩ := hz.1
    obtain ⟨q,hq,hf⟩ := hz.2
    refine ⟨t z,hk z,⟨typeTwoPairName p.val q.val,by
      change typeTwoLeftName (typeTwoPairName p.val q.val) ∈ δX.domain ∧
        typeTwoRightName (typeTwoPairName p.val q.val) ∈ δY.domain
      simpa only [typeTwoLeft_pair,typeTwoRight_pair] using And.intro p.property q.property⟩,?_,?_⟩
    · apply Prod.ext
      · simpa [typeTwoProductRepresentation] using hp
      · simpa [typeTwoProductRepresentation] using hq
    · simpa only [Nat.pair_unpair] using ht z.unpair.1 z.unpair.2 p.val q.val he hf

def computablePointSplit : Assembly.Hom
    (computablePointAssembly (typeTwoProductRepresentation δX δY))
    (Assembly.prod (computablePointAssembly δX) (computablePointAssembly δY)) :=
  (computablePointMap (hasComputableRealizer_fst δX δY)).pair
    (computablePointMap (hasComputableRealizer_snd δX δY))

theorem computablePointPair_split :
    (computablePointPair δX δY).comp (computablePointSplit δX δY) = Assembly.Hom.id _ := by
  apply Assembly.Hom.ext
  intro x
  apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem computablePointSplit_pair :
    (computablePointSplit δX δY).comp (computablePointPair δX δY) = Assembly.Hom.id _ := by
  apply Assembly.Hom.ext
  intro x
  exact Subtype.ext rfl

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Products of computable-point assemblies
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Given computable names of $x,y$, the preceding lemma produces a computable paired name of $(x,y)$. The total
    function $s$ tracks this map on the product assembly. Conversely, the two TTE coordinate projections induce
    assembly maps by the computable-point construction above. Pair these maps using the assembly product. The two
    composites are identity functions on the underlying points, hence identity assembly morphisms. This proves the
    claimed isomorphism without identifying a pair of name indices with an index of a paired name.
    \end{proof}
-/
def computablePointProductIso : CategoryTheory.Iso
    (Assembly.prod (computablePointAssembly δX) (computablePointAssembly δY))
    (computablePointAssembly (typeTwoProductRepresentation δX δY)) where
  hom := computablePointPair δX δY
  inv := computablePointSplit δX δY
  hom_inv_id := computablePointPair_split δX δY
  inv_hom_id := computablePointSplit_pair δX δY

end PolishSpaceBook.LambdaIndexPCA
