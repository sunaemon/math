module

public import PolishSpaceBook.FirstOrderTermModel

@[expose] public section

/-!
# Boolean clauses in a maximal consistent theory

Membership of sentences follows the truth tables. The reverse disjunction
clause uses a decision of the left disjunct; the implication clause discharges
an assumption, using either its consequence or its negation. These are purely
syntactic derivations and do not presuppose the term-model truth lemma.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

theorem binary_sentence (c : Connective) {φ ψ : AlphaFormula L}
    (hφ : φ ∈ Sentences L) (hψ : ψ ∈ Sentences L) : binary c φ ψ ∈ Sentences L := by
  change (binary c φ ψ).fv = ∅
  rw [fv_binary, hφ, hψ, Finset.union_empty]

namespace MaximallyConsistent
variable {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
include hT

theorem conj_mem_iff {φ ψ : AlphaFormula L} (hφ : φ ∈ Sentences L) (hψ : ψ ∈ Sentences L) :
    binary .conj φ ψ ∈ T ↔ φ ∈ T ∧ ψ ∈ T := by
  constructor
  · intro h
    exact ⟨hT.mem_of_proves hφ ((ProvesFrom.hyp h).map Derives.andLeft),
      hT.mem_of_proves hψ ((ProvesFrom.hyp h).map Derives.andRight)⟩
  · rintro ⟨hp, hq⟩
    exact hT.mem_of_proves (binary_sentence _ hφ hψ)
      ((ProvesFrom.hyp hp).map₂ (ProvesFrom.hyp hq) Derives.andIntro)

theorem disj_mem_iff {φ ψ : AlphaFormula L} (hφ : φ ∈ Sentences L) (hψ : ψ ∈ Sentences L) :
    binary .disj φ ψ ∈ T ↔ φ ∈ T ∨ ψ ∈ T := by
  constructor
  · intro h
    rcases hT.decides hφ with hp | hn
    · exact Or.inl hp
    · apply Or.inr
      apply hT.mem_of_proves hψ
      apply (ProvesFrom.hyp h).map₂ (ProvesFrom.hyp hn)
      intro Γ hd hneg
      apply Derives.orElim hd
      · exact .negElim ψ (.hyp Γ φ) (hneg.weaken (Finset.subset_insert _ _))
      · exact .hyp Γ ψ
  · intro h
    apply hT.mem_of_proves (binary_sentence _ hφ hψ)
    rcases h with hp | hq
    · exact (ProvesFrom.hyp hp).map (Derives.orLeft ψ)
    · exact (ProvesFrom.hyp hq).map (Derives.orRight φ)

theorem imp_mem_iff {φ ψ : AlphaFormula L} (hφ : φ ∈ Sentences L) (hψ : ψ ∈ Sentences L) :
    binary .imp φ ψ ∈ T ↔ (φ ∈ T → ψ ∈ T) := by
  constructor
  · intro hf hp
    exact hT.mem_of_proves hψ ((ProvesFrom.hyp hf).impElim (ProvesFrom.hyp hp))
  · intro h
    apply hT.mem_of_proves (binary_sentence _ hφ hψ)
    rcases hT.decides hφ with hp | hn
    · exact ProvesFrom.deduction.mp ((ProvesFrom.hyp (h hp)).mono (Set.subset_insert _ _))
    · apply (ProvesFrom.hyp hn).map
      intro Γ hneg
      exact .impIntro (.negElim ψ (.hyp Γ φ) (hneg.weaken (Finset.subset_insert _ _)))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    First record the membership rules in the maximal consistent theory. For sentences $A,B$,
    $$\begin{aligned}
    (A\land B)\in T^*&\iff A\in T^*\text{ and }B\in T^*,\\
    (A\lor B)\in T^*&\iff A\in T^*\text{ or }B\in T^*,\\
    (A\to B)\in T^*&\iff (A\in T^*\Rightarrow B\in T^*),\\
    \neg A\in T^*&\iff A\notin T^*.
    \end{aligned}$$
    Also $\bot\notin T^*$. Conjunction uses its introduction and elimination rules. For disjunction, decide $A$;
    if $\neg A\in T^*$, disjunction elimination gives $B$. The reverse implication uses disjunction introduction.
    For implication, the forward direction is modus ponens. Conversely, decide $A$: when $A\in T^*$ the hypothesis
    gives $B$, and otherwise $\neg A\in T^*$ makes the assumption $A$ contradictory. In either case implication
    introduction gives $A\to B$. The negation and falsity clauses follow from maximal consistency.
-/
theorem binary_mem_iff (c : Connective) {φ ψ : AlphaFormula L}
    (hφ : φ ∈ Sentences L) (hψ : ψ ∈ Sentences L) :
    binary c φ ψ ∈ T ↔ c.eval (φ ∈ T) (ψ ∈ T) := by
  cases c with
  | conj => exact hT.conj_mem_iff hφ hψ
  | disj => exact hT.disj_mem_iff hφ hψ
  | imp => exact hT.imp_mem_iff hφ hψ

end MaximallyConsistent
end PolishSpaceBook.NamedFirstOrder
