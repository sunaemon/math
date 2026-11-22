module

public import PolishSpaceBook.ForcingUnionNames
public import PolishSpaceBook.ForcingFormulaTruth
public import PolishSpaceBook.SetTheoryModelSchemes

@[expose] public section

/-! # A name selecting the elements satisfying a fixed formula in the extension -/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open FirstOrder Language ZFSet ForcingAtomic ForcingFormulas SetTheoryModels
universe u
variable (P M : ZFSet.{u}) [Preorder (Condition P)]

/-- Refine the old membership label and require the formula at the child name. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Define a subset of this product by
    $$\begin{aligned}
    \theta:=\{\langle\sigma,q\rangle\in A\times P:{}&\exists r\in P\,
     (\langle\sigma,r\rangle\in\tau\land q\le r\\
     &{}\land q\forces^*\varphi(\vec\nu,\sigma))\}.
    \end{aligned}$$
    The stronger label is essential: it must preserve the old membership witness and force the selecting formula.
-/
def separationName {n : ℕ} (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P M) : ZFSet.{u} :=
  (ZFSet.prod (childBound τ.val) P).sep (fun z =>
    ∃ (σ : Name P M) (q r : Condition P),
      z = pair σ.val q.val ∧ pair σ.val r.val ∈ τ.val ∧ q ≤ r ∧
        q ∈ force P M φ (Fin.snoc xs σ))

lemma pair_mem_separationName {n : ℕ} (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P M) (σ : Name P M) (q : Condition P) :
    pair σ.val q.val ∈ separationName P M τ φ xs ↔
      (∃ r : Condition P, pair σ.val r.val ∈ τ.val ∧ q ≤ r) ∧ q ∈ force P M φ (Fin.snoc xs σ) := by
  rw [separationName, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, σ', q', r, he, hπ, hqr, hφ⟩
    obtain ⟨hσ, hq⟩ := ZFSet.pair_inj.mp he
    have hs : σ = σ' := Subtype.ext hσ
    have hqq : q = q' := by cases q; cases q'; cases hq; rfl
    subst σ'
    subst q'
    exact ⟨⟨r, hπ, hqr⟩, hφ⟩
  · rintro ⟨⟨r, hπ, hqr⟩, hφ⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨child_mem_doubleUnion hπ, q.property⟩, σ, q, r, rfl, hπ, hqr, hφ⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Every pair in $\theta$ has a child name as its first coordinate and a condition in $P$ as its second, so
    $\theta$ is a name. This step uses the ground model's Separation, with no assumption that the extension already
    satisfies it.
-/
lemma separationName_isName {n : ℕ} (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P M) : IsName P (separationName P M τ φ xs) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, q, _, he⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
    exact ⟨σ, q, he⟩
  · intro σ q h
    obtain ⟨_, σ', q', r, he, _, _, _⟩ := ZFSet.mem_sep.mp h
    obtain ⟨hσ, hq⟩ := ZFSet.pair_inj.mp he
    exact ⟨hq.symm ▸ q'.property, hσ.symm ▸ σ'.property.2⟩

lemma mem_value_separationName_witnesses {n : ℕ} (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P M) (G : Order.PFilter (Condition P)) (x : ZFSet.{u}) :
    x ∈ value P G (separationName P M τ φ xs) ↔
      ∃ (σ : Name P M) (q r : Condition P), q ∈ G ∧ pair σ.val r.val ∈ τ.val ∧ q ≤ r ∧
        q ∈ force P M φ (Fin.snoc xs σ) ∧ value P G σ.val = x := by
  rw [mem_value]
  constructor
  · rintro ⟨σ, q, hqG, hpair, hx⟩
    obtain ⟨_, σ', q', r, he, hπ, hqr, hφ⟩ := ZFSet.mem_sep.mp hpair
    obtain ⟨hσ, hq⟩ := ZFSet.pair_inj.mp he
    have hqq : q = q' := by cases q; cases q'; cases hq; rfl
    subst q'
    exact ⟨σ', q, r, hqG, hπ, hqr, hφ, hσ ▸ hx⟩
  · rintro ⟨σ, q, r, hqG, hπ, hqr, hφ, hx⟩
    exact ⟨σ.val, q, hqG, (pair_mem_separationName P M τ φ xs σ q).mpr ⟨⟨r, hπ, hqr⟩, hφ⟩, hx⟩

/-- Directedness combines the membership label with the truth lemma's forcing condition. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Suppose $z\in\theta^G$. Choose $\langle\sigma,q\rangle\in\theta$ with $q\in G$ and $z=\sigma^G$, and take
    $r$ from the defining predicate. Since $q\le r$, upward closure puts $r$ in $G$, so $z\in\tau^G$.
    Also $q\forces^*\varphi(\vec\nu,\sigma)$. The truth theorem in §{sec:internal-generic-truth} gives
    $M[G]\models\varphi(\vec\nu^G,z)$.

    Conversely, let $z\in\tau^G$ satisfy $M[G]\models\varphi(\vec\nu^G,z)$.
    The valuation equation supplies $\langle\sigma,r\rangle\in\tau$ with $r\in G$ and $z=\sigma^G$.
    The child name belongs to the ground model. The truth theorem supplies $p\in G$ with
    $p\forces^*\varphi(\vec\nu,\sigma)$.
    Choose a common strengthening $q\in G$ with $q\le p,r$.
    Monotonicity gives $q\forces^*\varphi(\vec\nu,\sigma)$, and the child bound gives $\sigma\in A$.
    Thus $\langle\sigma,q\rangle\in\theta$, so $z\in\theta^G$. This proves the reverse inclusion.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $\ForcingSeparationName{\tau}{\varphi}{\vec\nu}$ for the name constructed in
    §{sec:generic-separation}. For every $M$-generic filter $G$, it satisfies
    $$\begin{aligned}
    \bigl(\ForcingSeparationName{\tau}{\varphi}{\vec\nu}\bigr)^G
    =\{z\in\tau^G:M[G]\models\varphi(\vec\nu^G,z)\}.
    \end{aligned}$$
    Thus a formula with ground-model parameter names selects a subset of the valuation of a fixed name.
-/
theorem mem_value_separationName (hM : M.IsTransitive) {n : ℕ}
    (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → Name P M)
    (G : Order.PFilter (Condition P)) (hG : MeetsFormulaTests P M G) (x : Extension P M G) :
    x.val ∈ value P G (separationName P M τ φ xs) ↔
      x.val ∈ value P G τ.val ∧ φ.Realize Empty.elim (Fin.snoc (fun i => evalName P M G (xs i)) x) := by
  rw [mem_value_separationName_witnesses]
  constructor
  · rintro ⟨σ, q, r, hqG, hπ, hqr, hφ, hx⟩
    have he : evalName P M G σ = x := Subtype.ext hx
    have ht := (formula_truth P M hM G hG φ (Fin.snoc xs σ)).mp ⟨q, hqG, hφ⟩
    rw [apply_snoc, he] at ht
    exact ⟨(mem_value P G τ.val x.val).mpr ⟨σ.val, r, G.mem_of_le hqr hqG, hπ, hx⟩, ht⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨σ, r, hrG, hπ, hx⟩ := (mem_value P G τ.val x.val).mp hx
    let σN : Name P M := ⟨σ, child_mem_ground hM τ.property.1 hπ, τ.property.2.child hπ⟩
    have he : evalName P M G σN = x := Subtype.ext hx
    have hassign := apply_snoc (evalName P M G) xs σN
    rw [he] at hassign
    rw [← hassign] at hφ
    obtain ⟨q, hqG, hq⟩ := (formula_truth P M hM G hG φ (Fin.snoc xs σN)).mpr hφ
    obtain ⟨s, hsG, hsq, hsr⟩ := G.directed q hqG r hrG
    exact ⟨σN, s, r, hsG, hπ, hsr, force_lower P M φ (Fin.snoc xs σN) hsq hq, hx⟩

/-- The selected name evaluates to the actual subset defined by the formula in the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    We verify the valuation identity
    $$\theta^G=\{z\in\tau^G:M[G]\models\varphi(\vec\nu^G,z)\}.$$
-/
theorem value_separationName (hM : M.IsTransitive) {n : ℕ}
    (τ : Name P M) (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → Name P M)
    (G : Order.PFilter (Condition P)) (hG : MeetsFormulaTests P M G) :
    value P G (separationName P M τ φ xs) = (value P G τ.val).sep
      (fun x => ∃ hx : x ∈ Extension P M G,
        φ.Realize Empty.elim (Fin.snoc (fun i => evalName P M G (xs i)) ⟨x, hx⟩)) := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hx
    have hxE : x ∈ Extension P M G := by
      obtain ⟨σ, _, _, _, _, _, _, he⟩ := (mem_value_separationName_witnesses P M τ φ xs G x).mp hx
      exact he ▸ (evalName P M G σ).property
    have h := (mem_value_separationName P M hM τ φ xs G hG ⟨x, hxE⟩).mp hx
    exact ⟨h.1, hxE, h.2⟩
  · rintro ⟨hx, hxE, hφ⟩
    exact (mem_value_separationName P M hM τ φ xs G hG ⟨x, hxE⟩).mpr ⟨hx, hφ⟩

end PolishSpaceBook.ForcingNames
