module

public import PolishSpaceBook.LambdaRealizers
public import PolishSpaceBook.RepresentedSubspaces

@[expose] public section

/-! # Reusing the same lambda program on represented subspaces -/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}

theorem HasComputableRealizer.restrict_source {δX : Representation X} {δY : Representation Y}
    {f : X → Y} (hf : HasComputableRealizer δX δY f) (A : Set X) :
    HasComputableRealizer (restrictedRepresentation δX A) δY (fun x => f x.val) := by
  obtain ⟨F, ⟨P, hP⟩, hF⟩ := hf
  exact ⟨fun p => F (restrictionOriginalName δX A p),
    ⟨P, hP.1, fun p n m => hP.2 (restrictionOriginalName δX A p) n m⟩,
    fun p => hF (restrictionOriginalName δX A p)⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For a restriction of the input space, reuse the same closed lambda term on the smaller set of valid names. Its exact-output property is retained on that domain. If the values of a map lie in the subspace, every output name of its realizer already belongs to the restricted output domain, so the same term realizes the map with that smaller codomain. Conversely, regard those same output names as names in the original space; their digits and computed values do not change. None of these operations tests membership in the subspace.
-/
theorem computable_subspace_target_iff (δX : Representation X) (δY : Representation Y)
    (A : Set Y) (f : X → A) :
    HasComputableRealizer δX (restrictedRepresentation δY A) f ↔
      HasComputableRealizer δX δY (fun x => (f x).val) := by
  constructor
  · rintro ⟨F, ⟨P, hP⟩, hF⟩
    refine ⟨fun p => restrictionOriginalName δY A (F p), ⟨P, hP⟩, ?_⟩
    intro p
    exact congrArg Subtype.val (hF p)
  · rintro ⟨F, ⟨P, hP⟩, hF⟩
    let G : δX.domain → (restrictedRepresentation δY A).domain := fun p =>
      ⟨(F p).val, (F p).property, (hF p).symm ▸ (f (δX.toFun p)).property⟩
    exact ⟨G, ⟨P, hP⟩, fun p => Subtype.ext (hF p)⟩
/-- Inclusion keeps the same input name and uses the identity lambda term. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Restriction of computable realizers
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The inclusion passes the input name through unchanged. The closed term $\lambdaab{o}{o}$ does this: after application to the name parameter and a numeral, one beta step exposes the requested input query.
-/
theorem computable_subspace_inclusion (δX : Representation X) (A : Set X) :
    HasComputableRealizer (restrictedRepresentation δX A) δX (Subtype.val : A → X) :=
  ⟨restrictionOriginalName δX A,
    ⟨NamedLambda.AlphaTerm.identityProgram,
      identityProgram_computes (restrictedRepresentation δX A).domain⟩,
    fun _ => rfl⟩
end PolishSpaceBook
