module

public import PolishSpaceBook.FirstOrderGraphProofs

@[expose] public section

/-!
# Proof-theoretic graph replacement from unique existence

Open the actual unique-existence abbreviation. Its comparison clause equates
every graph witness to the existential witness, hence to the specified term.
All freshness conditions for the two eigenvariables are explicit.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace Derives

/-- Unique existence and a known graph value give its universal characterization. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    First derive
    $$T\vdash\forall z\,(\rho\subst{y}{z}\to z=t).$$
    Open the unique-existence premise with temporary variable $y$. Its comparison clause is
    $\forall z\,(\rho\subst{y}{z}\to z=y)$. Instantiate it at $t$ and use the other premise to obtain $t=y$,
    hence $y=t$ by equality elimination. Here substitution through the fresh variable $z$ gives
    $(\rho\subst{y}{z})\subst{z}{t}=\rho\subst{y}{t}$ as $\alpha$-classes.
    Under the additional assumption $\rho\subst{y}{z}$, the comparison clause gives $z=y$, hence $z=t$.
    Discharge that assumption and universally quantify $z$. This is allowed because $z$ is not free in the
    temporary unique-existence assumption or in $T$. Eliminate the original existential assumption:
    $y$ is not free in the resulting universal formula, since it is absent from $t$ and distinct from $z$.
-/
theorem uniqueAt_specified_value {Γ : Context L} (ρ : AlphaFormula L) (x z : ℕ) (t : L.Term ℕ)
    (hxz : x ≠ z) (hxΓ : x ∉ Γ.fv) (hzΓ : z ∉ Γ.fv) (hzρ : z ∉ ρ.fv)
    (hxt : x ∉ t.varFinset) (hzt : z ∉ t.varFinset)
    (huniq : Derives Γ (uniqueAt x z ρ)) (hvalue : Derives Γ (ρ.subst x t)) :
    Derives Γ (quant .all z (binary .imp (ρ.subst x (.var z)) (equal (.var z) t))) := by
  let U := binary .conj ρ (quant .all z (binary .imp (ρ.subst x (.var z)) (equal (.var z) (.var x))))
  let F := quant .all z (binary .imp (ρ.subst x (.var z)) (equal (.var z) t))
  have hu : Derives (insert U Γ)
      (quant .all z (binary .imp (ρ.subst x (.var z)) (equal (.var z) (.var x)))) :=
    .andRight (.hyp Γ U)
  have htx : Derives (insert U Γ) (equal t (.var x)) := by
    apply Derives.impElim _ (hvalue.weaken (Finset.subset_insert _ _))
    simpa only [subst_binary, subst_equal, subst_via_fresh ρ x z t hzρ,
      termSubst_var_self, termSubst, Term.subst, ite_eq_right hxz, ite_true] using Derives.allElim z _ t hu
  have hxt' : Derives (insert U Γ) (equal (.var x) t) := by
    have h := Derives.eqElim (equal (.var z) t) z t (.var x)
      (by simpa only [subst_equal, termSubst_var_self, termSubst_not_free t z t hzt]
        using Derives.eqIntro (insert U Γ) t) htx
    simpa only [subst_equal, termSubst_var_self, termSubst_not_free t z (.var x) hzt] using h
  have hc : Derives (insert (ρ.subst x (.var z)) (insert U Γ)) (equal (.var z) t) := by
    have hzx : Derives (insert (ρ.subst x (.var z)) (insert U Γ)) (equal (.var z) (.var x)) :=
      .impElim (by simpa only [subst_self] using
        Derives.allElim z _ (.var z) (hu.weaken (Finset.subset_insert _ _))) (.hyp _ _)
    have h := Derives.eqElim (equal (.var z) (.var x)) x (.var x) t
      (by simpa only [subst_self] using hzx) (hxt'.weaken (Finset.subset_insert _ _))
    simpa only [subst_equal, termSubst_var_self, termSubst, Term.subst, ite_eq_right (Ne.symm hxz), ite_true] using h
  have hall : Derives (insert U Γ) F := by
    apply Derives.allIntro z (.impIntro hc)
    simp only [Context.fv_insert, U, fv_binary, fv_quant, Finset.mem_union, Finset.mem_erase,
      ne_eq, not_true_eq_false, false_and, or_false, not_or]
    exact ⟨hzρ,hzΓ⟩
  have hf : x ∉ F.fv := by
    have hρ := not_mem_fv_subst_self ρ x (Term.var z) (by simpa [Term.varFinset] using hxz)
    dsimp only [F]
    rw [fv_quant, fv_binary]
    change x ∉ ((ρ.subst x (.var z)).fv ∪ ({z} ∪ t.varFinset)).erase z
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, hρ, hxt, hxz,
      or_false, and_false, not_false_eq_true]
  apply Derives.exElim x x U F huniq (by simpa only [subst_self] using hall)
  simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
    false_and, or_false, not_or]
  exact ⟨hxΓ,hf⟩

/-- The unique-existence abbreviation suffices for both directions of graph replacement. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the forward implication, assume $\psi\subst{y}{t}$. Combine it with $\rho\subst{y}{t}$ and introduce
    the existential quantifier using $t$ as witness. Then discharge the added assumption.

    For the reverse implication, assume $\exists y\,(\rho\land\psi)$ and rename its bound variable to $z$.
    Open it with temporary assumption $\rho\subst{y}{z}\land\psi\subst{y}{z}$. The universal formula just
    derived gives $z=t$. Equality elimination in $\psi\subst{y}{z}$, followed by substitution through the
    fresh variable, gives $\psi\subst{y}{t}$. The variable $z$ is free in neither this conclusion nor $T$
    nor the added existential assumption, so existential elimination applies. Discharge that existential assumption.
    Conjunction introduction combines the two implications, which is the stated biconditional.
-/
theorem unique_graph_witness {Γ : Context L} (ρ ψ : AlphaFormula L) (x z : ℕ) (t : L.Term ℕ)
    (hxz : x ≠ z) (hxΓ : x ∉ Γ.fv) (hzΓ : z ∉ Γ.fv)
    (hzρ : z ∉ ρ.fv) (hzψ : z ∉ ψ.fv) (hxt : x ∉ t.varFinset) (hzt : z ∉ t.varFinset)
    (huniq : Derives Γ (uniqueAt x z ρ)) (hvalue : Derives Γ (ρ.subst x t)) :
    Derives Γ (binary .conj
      (binary .imp (ψ.subst x t) (quant .ex x (binary .conj ρ ψ)))
      (binary .imp (quant .ex x (binary .conj ρ ψ)) (ψ.subst x t))) := by
  have hb := uniqueAt_specified_value ρ x z t hxz hxΓ hzΓ hzρ hxt hzt huniq hvalue
  have h := graph_witness_equivalence (ρ.subst x (.var z)) (ψ.subst x (.var z)) z t hzΓ hzt
    (by simpa only [subst_via_fresh ρ x z t hzρ] using hvalue) hb
  have he : quant .ex x (binary .conj ρ ψ) =
      quant .ex z (binary .conj (ρ.subst x (.var z)) (ψ.subst x (.var z))) := by
    simpa only [subst_binary] using quant_rename .ex (binary .conj ρ ψ) x z
      (by simpa only [fv_binary, Finset.mem_union, not_or] using And.intro hzρ hzψ)
  simpa only [subst_via_fresh ψ x z t hzψ, ← he] using h

end Derives
namespace ProvesFrom

/-- For a theory of sentences, only the explicitly chosen comparison name needs to be kept fresh. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Graph replacement in proofs
-/
theorem unique_graph_witness {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ ψ : AlphaFormula L) (x z : ℕ) (t : L.Term ℕ) (hxz : x ≠ z)
    (hzρ : z ∉ ρ.fv) (hzψ : z ∉ ψ.fv) (hxt : x ∉ t.varFinset) (hzt : z ∉ t.varFinset)
    (huniq : ProvesFrom T (uniqueAt x z ρ)) (hvalue : ProvesFrom T (ρ.subst x t)) :
    ProvesFrom T (binary .conj
      (binary .imp (ψ.subst x t) (quant .ex x (binary .conj ρ ψ)))
      (binary .imp (quant .ex x (binary .conj ρ ψ)) (ψ.subst x t))) := by
  apply map₂_sentences hT huniq hvalue
  intro Γ hΓ hu hv
  exact Derives.unique_graph_witness ρ ψ x z t hxz (by rw [hΓ]; simp) (by rw [hΓ]; simp)
    hzρ hzψ hxt hzt hu hv

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
