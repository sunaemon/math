module

public import PolishSpaceBook.ComputablePolishSpacesTTE

@[expose] public section

/-! # Continuous realizers, independently of any execution model -/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}

/-- Continuity concerns the actual partial name realizer. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    *   \termdefine{continuously realizable} if some continuous $F$ realizes it;
    *   \termdefine{computably realizable} if some \termuse{Type-Two lambda realizer} computes such an $F$.
-/
def HasContinuousRealizer (δX : Representation X) (δY : Representation Y) (f : X → Y) : Prop :=
  ∃ F : δX.domain → δY.domain, Continuous (fun p => (F p).val) ∧ Realizes δX δY F f

def ContinuouslyRealizableMap (δX : Representation X) (δY : Representation Y) :=
  {f : X → Y // HasContinuousRealizer δX δY f}

end PolishSpaceBook
