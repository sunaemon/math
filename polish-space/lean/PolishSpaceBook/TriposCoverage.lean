module

public import PolishSpaceBook.LambdaRealizabilityUncurrying

@[expose] public section

namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER
universe u

/-- The semantic witness relation is existentially quantified; the numerical
realizer itself contains only the two component realizers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    For a functional relation $F:Z\to\RealizabilityFunctionSpace{X}{Y}$, define its application relation by
    $$\UncurriedRelation{F}((z,x),y):=
     \bigcup_{R\in|\RealizabilityFunctionSpace{X}{Y}|}\bigl(F(z,R)\land R(x,y)\bigr).$$
    Its realizers are numerical pairs $\NatPair{a}{b}$. The relation $R$ witnessing membership is not part of the code.
-/
theorem uncurryRelation_mem_iff {Z X Y : RealizerPER.{u}}
    (F : FunctionalRelation Z (functionSpace X Y)) (z : Z.Carrier) (x : X.Carrier)
    (y : Y.Carrier) (n : ℕ) :
    n ∈ (uncurryRelation F).val (z, x) y ↔
      ∃ R a, a ∈ F.val z R ∧ ∃ b, b ∈ R x y ∧ n = Nat.pair a b := by
  constructor
  · rintro ⟨R, ha, hb⟩
    exact ⟨R, n.unpair.1, ha, n.unpair.2, hb, (Nat.pair_unpair n).symm⟩
  · rintro ⟨R, a, ha, b, hb, rfl⟩
    exact ⟨R, by simpa using ha, by simpa using hb⟩

end PolishSpaceBook.LambdaIndexPCA
