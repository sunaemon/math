module

public import PolishSpaceBook.AssemblyProducts
public import PolishSpaceBook.PCACases

@[expose] public section

/-! # Tagged binary coproducts and finite coproducts of assemblies -/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the binary coproduct, use the disjoint union $|X|\disjointUnion|Y|$ with injections $i,j$ and prescribe
    $$\begin{aligned}
    \PCAPair{\mathsf k}{a}&\Vdash_{X+Y}i(x)
    &&\text{when }a\Vdash_X x,\\
    \PCAPair{\mathsf q}{b}&\Vdash_{X+Y}j(y)
    &&\text{when }b\Vdash_Y y.
    \end{aligned}$$
    These are exactly the realizers of the indicated elements. Each realizer set is nonempty, and the injections
    are tracked by $\mathsf p\mathsf k$ and $\mathsf p\mathsf q$ respectively.
-/
def coproduct (X Y : Assembly.{u,v} K) : Assembly.{u,v} K where
  Carrier := X.Carrier ⊕ Y.Carrier
  realizes a := Sum.elim
    (fun x => ∃ b, a = K.pair K.k b ∧ X.realizes b x)
    (fun y => ∃ b, a = K.pair K.secondSelector b ∧ Y.realizes b y)
  inhabited := by
    intro z
    cases z with
    | inl x => obtain ⟨b,hb⟩ := X.inhabited x; exact ⟨K.pair K.k b,b,rfl,hb⟩
    | inr y => obtain ⟨b,hb⟩ := Y.inhabited y; exact ⟨K.pair K.secondSelector b,b,rfl,hb⟩

def inLeft (X Y : Assembly.{u,v} K) : X ⟶ coproduct X Y where
  toFun := Sum.inl
  tracked := ⟨K.pairLeft K.k,fun _x a ha => ⟨K.pair K.k a,K.application_pairLeft _ _,a,rfl,ha⟩⟩

def inRight (X Y : Assembly.{u,v} K) : Y ⟶ coproduct X Y where
  toFun := Sum.inr
  tracked := ⟨K.pairLeft K.secondSelector,
    fun _y a ha => ⟨K.pair K.secondSelector a,K.application_pairLeft _ _,a,rfl,ha⟩⟩

def coproductDesc {X Y Z : Assembly.{u,v} K} (f : X ⟶ Z) (g : Y ⟶ Z) : coproduct X Y ⟶ Z where
  toFun := Sum.elim f g
  tracked := by
    obtain ⟨r,hr⟩ := f.tracked
    obtain ⟨s,hs⟩ := g.tracked
    refine ⟨K.casesTracker r s,?_⟩
    intro z a ha
    cases z with
    | inl x =>
      obtain ⟨b,rfl,hb⟩ := ha
      obtain ⟨c,hc,hz⟩ := hr x b hb
      exact ⟨c,(K.application_casesTracker_left r s b).trans hc,hz⟩
    | inr y =>
      obtain ⟨b,rfl,hb⟩ := ha
      obtain ⟨c,hc,hz⟩ := hs y b hb
      exact ⟨c,(K.application_casesTracker_right r s b).trans hc,hz⟩

def coproductIsColimit (X Y : Assembly.{u,v} K) :
    IsColimit (BinaryCofan.mk (inLeft X Y) (inRight X Y)) :=
  BinaryCofan.isColimitMk (fun s => coproductDesc s.inl s.inr)
    (fun _ => Hom.ext (fun _ => rfl)) (fun _ => Hom.ext (fun _ => rfl)) (by
      intro s m hl hr
      apply Hom.ext
      intro z
      cases z with
      | inl x => exact congrArg (fun q : X ⟶ s.pt => q x) hl
      | inr y => exact congrArg (fun q : Y ⟶ s.pt => q y) hr)

instance assemblyHasColimitPair (X Y : Assembly.{u,v} K) : HasColimit (pair X Y) :=
  HasColimit.mk ⟨_,coproductIsColimit X Y⟩

instance assemblyHasBinaryCoproducts : HasBinaryCoproducts (Assembly.{u,v} K) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance assemblyHasFiniteCoproducts : HasFiniteCoproducts (Assembly.{u,v} K) :=
  hasFiniteCoproducts_of_has_binary_and_initial

end PolishSpaceBook.Assembly
