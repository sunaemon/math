module

public import PolishSpaceBook.RepresentedContinuousMaps

@[expose] public section

/-! # Continuous maps between admissibly represented spaces -/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [SequentialSpace X] [TopologicalSpace Y]

/-- Continuity descends along the input representation's quotient map. -/
theorem HasContinuousRealizer.continuous {δX : Representation X}
    {δY : Representation Y} {f : X → Y}
    (hf : HasContinuousRealizer δX δY f) (hX : δX.IsAdmissible)
    (hY : δY.IsContinuous) : Continuous f := by
  obtain ⟨F, hF, hf⟩ := hf
  have hFc : Continuous F := hF.subtype_mk _
  apply (isQuotientMap_of_admissible δX hX).continuous_iff.mpr
  have he : f ∘ δX.toFun = δY.toFun ∘ F := funext fun p => (hf p).symm
  rw [he]
  exact hY.comp hFc

omit [SequentialSpace X] in
/-- Lift the continuous partial map on the input name domain through admissibility. -/
theorem continuous_hasContinuousRealizer {δX : Representation X}
    {δY : Representation Y} {f : X → Y} (hf : Continuous f)
    (hX : δX.IsContinuous) (hY : δY.IsAdmissible) :
    HasContinuousRealizer δX δY f := by
  obtain ⟨F, hF, heq⟩ := (admissible_iff_partial_lifting δY).mp hY |>.2
    δX.domain (f ∘ δX.toFun) (hf.comp hX)
  exact ⟨F, continuous_subtype_val.comp hF, heq⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: recall
  title: Continuous-realizer characterization
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Suppose first that $F$ is a continuous realizer of $f:X\to Y$. If $U\IncludedIn Y$ is
    open, then, restricting the inverse image under $F$ to $\DomainOf{\delta_X}$,
    $$
    \delta_X^{-1}(f^{-1}(U))=F^{-1}(\delta_Y^{-1}(U))
    $$
    is open in $\DomainOf{\delta_X}$. The final topology induced by $\delta_X$ therefore makes $f^{-1}(U)$ open. Conversely,
    if $f$ is continuous, then $f\circ\delta_X:\DomainOf{\delta_X}\to Y$ is a continuous partial map. The partial-map form
    of admissibility recalled in §{sec:kreitz-weihrauch-admissibility} gives a continuous map
    $F:\DomainOf{\delta_X}\to\DomainOf{\delta_Y}$ with $\delta_Y\circ F=f\circ\delta_X$, so $F$ realizes $f$.
-/
/-- Sequentiality of the input suffices; in particular the theorem applies to Polish spaces. -/
theorem hasContinuousRealizer_iff_continuous (δX : Representation X)
    (δY : Representation Y) (hX : δX.IsAdmissible) (hY : δY.IsAdmissible)
    (f : X → Y) : HasContinuousRealizer δX δY f ↔ Continuous f :=
  ⟨fun hf => hf.continuous hX hY.1, fun hf => continuous_hasContinuousRealizer hf hX.1 hY⟩

end PolishSpaceBook
