module

public import PolishSpaceBook.SetTheoryCollection
public import PolishSpaceBook.ForcingPowerSet

@[expose] public section

/-! # Collecting forcing witnesses and preserving the full Replacement schema -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

def forcingWitnessParams {α : Type*} {n : ℕ} (xs : Fin n → α) (P R : α) : Fin (n + 2) → α :=
  Fin.snoc (Fin.snoc xs P) R

/-- Free variables are ps,P,R,a,b; the final two bound variables are σ,q. -/
def forcingWitnessIndex (n : ℕ) : Fin (n + 5) → Fin (n + 6) :=
  forcingAssignment
    (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 4)).castSucc) (Fin.last (n + 3)).castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc (Fin.last (n + 5))

lemma forcingWitness_reindex {α : Type*} {n : ℕ} (xs : Fin n → α) (P R a b σ q : α) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (forcingWitnessParams xs P R) a) b) σ) q ∘
      forcingWitnessIndex n) = forcingAssignment (Fin.snoc (Fin.snoc xs σ) b) P R q := by
  simp only [forcingWitnessIndex, forcingWitnessParams, forcingAssignment, Function.comp_def,
    apply_snoc, Fin.snoc_castSucc, Fin.snoc_last]

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For the internal Collection argument, define a relation on a coded input $d$ and an output name $\nu$:
    $$\begin{aligned}
    \Psi(d,\nu)\;:\equiv\;&\eta(P,\nu)\land\exists\sigma\,\exists q\in P\\
     &\bigl[d=\langle\sigma,q\rangle\land\eta(P,\sigma)\\
     &{}\land\rho_\varphi(P,R,q,\vec\xi,\sigma,\nu)\bigr].
    \end{aligned}$$
    Here $\eta$ and $\rho_\varphi$ are the actual first-order defining formulas from
    §{sec:internal-forcing-formulas}; the parameters are $P,R,\vec\xi$.
-/
def forcingWitnessFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    ForcingFormulas.Formula (n + 4) :=
  (memberAt (Fin.last (n + 5)) (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc ⊓
    orderedPairFormula (Fin.last (n + 2)).castSucc.castSucc.castSucc
      (Fin.last (n + 4)).castSucc (Fin.last (n + 5)) ⊓
    reindex nameFormula ![(Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc,
      (Fin.last (n + 4)).castSucc] ⊓
    reindex nameFormula ![(Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc,
      (Fin.last (n + 3)).castSucc.castSucc] ⊓
    reindex (forcingTranslation φ) (forcingWitnessIndex n)).ex.ex

lemma realize_forcingWitnessFormula_aux {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (P R a b : M) :
    (forcingWitnessFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc (forcingWitnessParams ps P R) a) b) ↔
      ∃ σ q : M, q.val ∈ P.val ∧ a.val = pair σ.val q.val ∧
        nameFormula.Realize Empty.elim ![P, σ] ∧ nameFormula.Realize Empty.elim ![P, b] ∧
        (forcingTranslation φ).Realize Empty.elim (forcingAssignment (Fin.snoc (Fin.snoc ps σ) b) P R q) := by
  simp only [forcingWitnessFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_memberAt_model, realize_orderedPair_model hM, realize_reindex,
    Function.comp_def, apply_pair_assignment, forcingWitnessParams, Fin.snoc_castSucc, Fin.snoc_last,
    and_assoc]
  simp only [forcingWitnessIndex, forcingAssignment, apply_snoc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Image membership, with free variables ps,x,b and an input quantified over x. -/
def imageMemberFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  boundedExists (Fin.last n).castSucc
    (reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n + 2))) (Fin.last (n + 1)).castSucc))

lemma realize_imageMemberFormula (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → S) (x b : S) :
    (imageMemberFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps x) b) ↔
      ∃ a : S, a.val ∈ x.val ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [imageMemberFormula, realize_boundedExists_model, realize_reindex, Function.comp_def,
    apply_snoc, Fin.snoc_castSucc, Fin.snoc_last]

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hM hinf hpair hunion hpower hsep hrep hR

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For $\sigma,\nu\in M^P$ and $q\in P$, their interpretation is exactly
    $$M\models\Psi(\langle\sigma,q\rangle,\nu)
     \quad\Longleftrightarrow\quad q\forces^*\varphi(\vec\xi,\sigma,\nu).$$
    The name clauses ensure that all possible output witnesses are actual names.
-/
lemma realize_forcingWitnessFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (xs : Fin n → Name P.val M) (a b : M) :
    (forcingWitnessFormula φ).Realize Empty.elim
      (Fin.snoc (Fin.snoc (forcingWitnessParams (fun i => nameInModel (xs i)) P R) a) b) ↔
      ∃ (σ : Name P.val M) (q : Condition P.val) (hb : IsName P.val b.val),
        a.val = pair σ.val q.val ∧
          q ∈ force P.val M φ (Fin.snoc (Fin.snoc xs σ) ⟨b.val, b.property, hb⟩) := by
  rw [realize_forcingWitnessFormula_aux hM]
  constructor
  · rintro ⟨σ, q, hqP, ha, hσ, hb, hφ⟩
    have hσn := (name_definable hM hinf hpair hunion hpower hsep hrep P σ).mp hσ
    have hbn := (name_definable hM hinf hpair hunion hpower hsep hrep P b).mp hb
    let σN : Name P.val M := ⟨σ.val, σ.property, hσn⟩
    let bN : Name P.val M := ⟨b.val, b.property, hbn⟩
    let qc : Condition P.val := ⟨q.val, hqP⟩
    refine ⟨σN, qc, hbn, ha, ?_⟩
    apply (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ
      (Fin.snoc (Fin.snoc xs σN) bN) qc).mp
    rw [apply_snoc, apply_snoc]
    simpa only [nameInModel, σN, bN, qc] using hφ
  · rintro ⟨σ, q, hb, ha, hφ⟩
    have ht := (forcing_definable hM hinf hpair hunion hpower hsep hrep P R hR φ
      (Fin.snoc (Fin.snoc xs σ) ⟨b.val, b.property, hb⟩) q).mpr hφ
    refine ⟨nameInModel σ, ⟨q.val, hM.mem_trans q.property P.property⟩, q.property, ha,
      (name_definable hM hinf hpair hunion hpower hsep hrep P (nameInModel σ)).mpr σ.property.2,
      (name_definable hM hinf hpair hunion hpower hsep hrep P b).mpr hb, ?_⟩
    rw [apply_snoc, apply_snoc] at ht
    simpa only [nameInModel] using ht

/-- One ground set supplies a witness for every satisfiable condition/input-name pair in a fixed bound. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply §{sec:internal-collection} to $D$ and $\Psi$.
    We obtain $W\in M$ such that, for every $\sigma\in A\cap M^P$ and $q\in P$,
    $$\begin{aligned}
    &\exists\nu\in M^P\;q\forces^*\varphi(\vec\xi,\sigma,\nu)\\
    &\quad\Longrightarrow\exists\nu'\in W\cap M^P\;
     q\forces^*\varphi(\vec\xi,\sigma,\nu').
    \end{aligned}$$
    The condition $q$ and input name $\sigma$ are preserved: equality of their ordered-pair codes identifies
    both coordinates. No uniform choice of $\nu'$ is needed.
-/
theorem collect_forcing_witnesses {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (xs : Fin n → Name P.val M) (A : M) :
    ∃ W : M, ∀ (σ : Name P.val M) (q : Condition P.val), pair σ.val q.val ∈ A.val →
      (∃ ν : Name P.val M, q ∈ force P.val M φ (Fin.snoc (Fin.snoc xs σ) ν)) →
      ∃ ν : Name P.val M, ν.val ∈ W.val ∧ q ∈ force P.val M φ (Fin.snoc (Fin.snoc xs σ) ν) := by
  obtain ⟨W, hW⟩ := strong_collection_in_model hM hinf hpair hunion hpower hsep hrep
    (forcingWitnessFormula φ) (forcingWitnessParams (fun i => nameInModel (xs i)) P R) A
  refine ⟨W, ?_⟩
  intro σ q ha hex
  let a : M := ⟨pair σ.val q.val, hM.mem_trans ha A.property⟩
  have hab : ∃ b : M, (forcingWitnessFormula φ).Realize Empty.elim
      (Fin.snoc (Fin.snoc (forcingWitnessParams (fun i => nameInModel (xs i)) P R) a) b) := by
    obtain ⟨ν, hν⟩ := hex
    exact ⟨nameInModel ν, (realize_forcingWitnessFormula hM hinf hpair hunion hpower hsep hrep P R hR
      φ xs a (nameInModel ν)).mpr ⟨σ, q, ν.property.2, rfl, hν⟩⟩
  obtain ⟨b, hbW, hb⟩ := hW a ha hab
  obtain ⟨σ', q', hbN, he, hf⟩ :=
    (realize_forcingWitnessFormula hM hinf hpair hunion hpower hsep hrep P R hR φ xs a b).mp hb
  obtain ⟨hσ, hq⟩ := ZFSet.pair_inj.mp he
  have hσσ : σ = σ' := Subtype.ext hσ
  have hqq : q = q' := by cases q; cases q'; cases hq; rfl
  subst σ'
  subst q'
  exact ⟨⟨b.val, b.property, hbN⟩, hbW, hf⟩

/-- Collect names for all outputs, then separate the exact image inside their evaluated bound. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Put $K:=\bigcup W\in M$ and repeat the bounded-name construction of §{sec:generic-power-set}:
    $$\begin{aligned}
    C&:=\{\nu\in\InternalPowerSet{M}{K}:M\models\eta(P,\nu)\}\in M,\\
    \Pi&:=C\times P\in M^P.
    \end{aligned}$$
    Every name $\nu\in W$ is a subset of $K$, so $\nu\in C$ and $\nu^G\in\Pi^G$.
    We show that this evaluated name contains every output of the given functional relation.

    Suppose $a\in x$ and $M[G]\models\varphi(\vec p,a,b)$.
    The valuation equation gives $\langle\sigma,r\rangle\in\tau$ with $r\in G$ and $\sigma^G=a$;
    the child-name lemma puts $\sigma$ in $A\cap M^P$.
    Choose a name $\nu\in M^P$ for $b$.
    The truth theorem gives $q\in G$ with $q\forces^*\varphi(\vec\xi,\sigma,\nu)$.
    Since $\langle\sigma,q\rangle\in D$, the property of $W$ supplies $\nu'\in W\cap M^P$ such that the same $q$ forces
    this name to satisfy the same relation.
    The truth theorem now gives $M[G]\models\varphi(\vec p,a,\nu'^G)$.
    Uniqueness of the output in $M[G]$ implies $\nu'^G=b$, so $b\in\Pi^G$.
    This is where functionality is used; the collected relation in $M$ was allowed to have many output names.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Finally apply Separation in $M[G]$ to the set $\Pi^G$, using the formula
    $\exists a\in x\,\varphi(\vec p,a,b)$ with parameters $\vec p,x$. This gives
    $$Y:=\{b\in\Pi^G:M[G]\models\exists a\in x\,\varphi(\vec p,a,b)\}\in M[G].$$
    The preceding bound proves, for all $b\in M[G]$,
    $$b\in Y\quad\Longleftrightarrow\quad M[G]\models\exists a\in x\,\varphi(\vec p,a,b).$$
    This is the required Replacement instance. Every finite tuple of extension parameters has ground-model names,
    so the argument proves the entire schema.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Fix $x\in M[G]$, a finite tuple $\vec p$ of parameters from $M[G]$, and a formula
    $\varphi(\vec p,a,b)$ satisfying
    $$M[G]\models\forall a\in x\,\exists!b\,\varphi(\vec p,a,b).$$
    Choose names $\tau,\vec\xi\in M^P$ with $x=\tau^G$ and $\vec p=\vec\xi^G$.
    Put
    $$A:=\bigcup\bigcup\tau,\qquad D:=A\times P\in M.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Replacement in generic extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The Collection argument in §{sec:generic-replacement} bounds output names and proves the full Replacement schema.
-/
theorem extension_models_replacement (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : Extension P.val M G ⊨ replacementSentence φ := by
  classical
  apply (realize_replacement _ φ).mpr
  intro ps x htotal
  choose xs hxs using fun i => evalName_surjective P.val M G (ps i)
  obtain ⟨τ, hτ⟩ := evalName_surjective P.val M G x
  have hps : (fun i => evalName P.val M G (xs i)) = ps := funext hxs
  have hx : value P.val G τ.val = x.val := congrArg Subtype.val hτ
  let A := childBound τ.val
  have hA : A ∈ M := union_mem hM hunion (union_mem hM hunion τ.property.1)
  let D := ZFSet.prod A P.val
  have hD : D ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _) hA P.property
  obtain ⟨W, hW⟩ := collect_forcing_witnesses hM hinf hpair hunion hpower hsep hrep P R hR φ xs ⟨D, hD⟩
  let K := ZFSet.sUnion W.val
  have hK : K ∈ M := union_mem hM hunion W.property
  let piName : Name P.val M := ⟨boundedNamesName P.val M K,
    boundedNamesName_mem hM hinf hpair hunion hpower hsep hrep P hK,
    boundedNamesName_isName P.val M K⟩
  have ht := modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG
  have hbound (b : Extension P.val M G)
      (hb : ∃ a : Extension P.val M G, a.val ∈ x.val ∧
        φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
      b.val ∈ (evalName P.val M G piName).val := by
    obtain ⟨a, ha, hab⟩ := hb
    have haτ : a.val ∈ value P.val G τ.val := hx.symm ▸ ha
    obtain ⟨σ, r, _, hσr, heσ⟩ := (mem_value P.val G τ.val a.val).mp haτ
    let σN : Name P.val M := ⟨σ, child_mem_ground hM τ.property.1 hσr, τ.property.2.child hσr⟩
    have hσa : evalName P.val M G σN = a := Subtype.ext heσ
    obtain ⟨ν, hν⟩ := evalName_surjective P.val M G b
    let ns : Fin (n + 2) → Name P.val M := Fin.snoc (Fin.snoc xs σN) ν
    have hab' : φ.Realize Empty.elim (fun i => evalName P.val M G (ns i)) := by
      change φ.Realize Empty.elim (evalName P.val M G ∘ ns)
      dsimp only [ns, Function.comp_def]
      rw [apply_snoc, apply_snoc, hps, hσa, hν]
      exact hab
    obtain ⟨q, hqG, hq⟩ := (formula_truth P.val M hM G ht φ (Fin.snoc (Fin.snoc xs σN) ν)).mpr hab'
    have hpairD : pair σN.val q.val ∈ D :=
      ZFSet.pair_mem_prod.mpr ⟨child_mem_doubleUnion hσr, q.property⟩
    obtain ⟨ν', hν'W, hν'⟩ := hW σN q hpairD ⟨ν, hq⟩
    have hab'' := (formula_truth P.val M hM G ht φ (Fin.snoc (Fin.snoc xs σN) ν')).mp ⟨q, hqG, hν'⟩
    rw [apply_snoc, apply_snoc, hps, hσa] at hab''
    obtain ⟨c, _, huniq⟩ := htotal a ha
    have he : evalName P.val M G ν' = b := (huniq _ hab'').trans (huniq _ hab).symm
    apply (mem_value_boundedNamesName P.val M K G b.val).mpr
    refine ⟨ν', ?_, congrArg Subtype.val he⟩
    intro z hz
    exact ZFSet.mem_sUnion.mpr ⟨ν'.val, hν'W, hz⟩
  have hsepE := extension_models_separation hM hinf hpair hunion hpower hsep hrep P R hR G hG
    (imageMemberFormula φ)
  obtain ⟨Y, hY⟩ := (realize_separation _ (imageMemberFormula φ)).mp hsepE (Fin.snoc ps x)
    (evalName P.val M G piName)
  refine ⟨Y, fun b => ?_⟩
  rw [hY, realize_imageMemberFormula]
  exact ⟨And.right, fun hb => ⟨hbound b hb, hb⟩⟩

end Model
end PolishSpaceBook.SetTheoryModels
