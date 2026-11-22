module

public import PolishSpaceBook.SetTheoryInternalTreeBranches

@[expose] public section

/-! # Branch existence is absolute between transitive models

When the smaller model has no branch, construct its ordinal-valued rank graph,
transfer that same certificate to the larger model, and exclude a branch there.
The certificate, rather than merely the final well-foundedness proposition,
is retained throughout this argument.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BorelExpression
universe u

/-- The branch's whole function graph must belong to the indicated model. -/
def HasInternalTreeBranch (M : ZFSet.{u}) (T : Set (List ℕ)) : Prop :=
  ∃ p : ℕ → ℕ, p ∈ treeBody T ∧ pointGraph p ∈ M

/-- A fixed numerical coding of a countable move alphabet. -/
def codedMoveTree {A : Type*} (e : A ≃ ℕ) (T : Set (List A)) : Set (List ℕ) :=
  List.map e '' T

lemma codedMoveTree_subtree {A : Type*} (e : A ≃ ℕ) (T : Set (List A)) (hT : IsSubtree T) :
    IsSubtree (codedMoveTree e T) := by
  rintro s t ⟨v, hv, rfl⟩ hst
  refine ⟨v.take s.length, hT hv (List.take_prefix _ _), ?_⟩
  rw [List.map_take]
  exact (List.prefix_iff_eq_take.mp hst).symm

lemma treeBody_codedMoveTree {A : Type*} (e : A ≃ ℕ) (T : Set (List A)) (p : ℕ → A) :
    (e ∘ p) ∈ treeBody (codedMoveTree e T) ↔ p ∈ treeBody T := by
  have hp (n : ℕ) : seqPrefix (e ∘ p) n = (seqPrefix p n).map e := by
    simp only [seqPrefix, List.map_ofFn, Function.comp_def]
  constructor
  · intro h n
    obtain ⟨v, hv, he⟩ := h n
    have heq := (List.map_injective_iff.mpr e.injective) (he.trans (hp n))
    exact heq ▸ hv
  · intro h n
    exact ⟨seqPrefix p n, h n, (hp n).symm⟩

lemma internal_codedMoveTree_iff {A : Type*} (M : ZFSet.{u}) (e : A ≃ ℕ) (T : Set (List A)) :
    (∃ p : ℕ → A, p ∈ treeBody T ∧ pointGraph (e ∘ p) ∈ M) ↔
      HasInternalTreeBranch M (codedMoveTree e T) := by
  constructor
  · rintro ⟨p, hp, hm⟩
    exact ⟨e ∘ p, (treeBody_codedMoveTree e T p).mpr hp, hm⟩
  · rintro ⟨q, hq, hm⟩
    have he : e ∘ (e.symm ∘ q) = q := by funext n; simp
    refine ⟨e.symm ∘ q, ?_, by simpa only [he] using hm⟩
    apply (treeBody_codedMoveTree e T _).mp
    simpa only [he] using hq

variable {M N : ZFSet.{u}} (hM : M.IsTransitive) (hN : N.IsTransitive) (hMN : M ⊆ N)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

include hM hinf hpair hunion hpower hsep hrep hchoice

/-- Internal absence of a branch supplies an actual rank graph in M. -/
theorem internal_tree_rank_exists (T : Set (List ℕ)) (hT : IsSubtree T)
    (hW : wordTreeSet.{u} T ∈ M) (hno : ¬ HasInternalTreeBranch M T) :
    ∃ α f : M, IsRankCertificate (wordTreeSet T) (wordExtensionRelation (wordTreeSet T)) α.val f.val := by
  let W : M := ⟨wordTreeSet T, hW⟩
  let R : M := ⟨wordExtensionRelation W.val,
    wordExtensionRelation_mem hM hpair hunion hpower hsep hW⟩
  have hmin := internal_tree_minima_of_no_internal_branch hM hinf hpair hunion hpower hsep
    hchoice T hT W R rfl rfl hno
  obtain ⟨α, f, hr⟩ := internal_rank_certificate hM hinf hpair hunion hpower hsep hrep hchoice W R hmin
  exact ⟨α, f, (realize_rankCertificateFormula hM W R α f).mp hr⟩

include hN hMN

/-- The same ordinal and function graph are recognized as a rank in N. -/
theorem internal_tree_rank_transfers (T : Set (List ℕ)) (hT : IsSubtree T)
    (hW : wordTreeSet.{u} T ∈ M) (hno : ¬ HasInternalTreeBranch M T) :
    ∃ α f : M, rankCertificateFormula.Realize Empty.elim
      ![(⟨wordTreeSet T, hMN hW⟩ : N),
        (⟨wordExtensionRelation (wordTreeSet T),
          hMN (wordExtensionRelation_mem hM hpair hunion hpower hsep hW)⟩ : N),
        (⟨α.val, hMN α.property⟩ : N), (⟨f.val, hMN f.property⟩ : N)] := by
  obtain ⟨α, f, hr⟩ := internal_tree_rank_exists hM hinf hpair hunion hpower hsep hrep hchoice T hT hW hno
  exact ⟨α, f, (realize_rankCertificateFormula hN _ _ _ _).mpr hr⟩

/-- An old branch remains available; if there is none, its old rank excludes
all branches in the larger model. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] If $M$ has a branch, its function graph belongs to $M$ and therefore to $N$.
    Conversely, suppose $M$ has no branch through $T$. The internal dependent-choice argument in
    §{sec:internal-tree-branches} shows that the strict-extension relation on its nodes satisfies the internal
    subset-minimum condition: a nonempty internal subset without a minimum would produce a branch in $M$.
    The construction in §{sec:internal-rank-existence} therefore gives an ordinal $\alpha\in M$ and a function graph
    $\rho:T\to\alpha$ in $M$ that strictly decreases along proper extensions. We use this decreasing-rank property;
    no choice of a canonical least rank is needed. §{sec:internal-rank-certificates} transfers the same
    ordinal and graph to $N$. An infinite branch in $N$ would give an infinite decreasing sequence of ordinals,
    which is impossible. For trees on $\omega\times\omega$, use the same fixed numerical pairing to code nodes and
    branches in both models.
-/
theorem tree_branch_absolute (T : Set (List ℕ)) (hT : IsSubtree T)
    (hW : wordTreeSet.{u} T ∈ M) : HasInternalTreeBranch M T ↔ HasInternalTreeBranch N T := by
  constructor
  · rintro ⟨p, hp, hpm⟩
    exact ⟨p, hp, hMN hpm⟩
  · intro hn
    by_contra hm
    obtain ⟨α, f, hr⟩ := internal_tree_rank_transfers hM hN hMN hinf hpair hunion hpower hsep hrep
      hchoice T hT hW hm
    have hno := no_branch_of_internal_tree_rank hN T hT
      ⟨wordTreeSet T, hMN hW⟩
      ⟨wordExtensionRelation (wordTreeSet T),
        hMN (wordExtensionRelation_mem hM hpair hunion hpower hsep hW)⟩
      ⟨α.val, hMN α.property⟩ ⟨f.val, hMN f.property⟩ rfl rfl hr
    exact hno ⟨hn.choose, hn.choose_spec.1⟩

/-- In particular this covers the product alphabet ℕ × ℕ via numerical pairing.
The same fixed coding represents the tree and every branch in both models. -/
theorem countable_tree_branch_absolute {A : Type*} (e : A ≃ ℕ) (T : Set (List A))
    (hT : IsSubtree T) (hW : wordTreeSet (codedMoveTree e T) ∈ M) :
    (∃ p : ℕ → A, p ∈ treeBody T ∧ pointGraph (e ∘ p) ∈ M) ↔
      ∃ p : ℕ → A, p ∈ treeBody T ∧ pointGraph (e ∘ p) ∈ N := by
  rw [internal_codedMoveTree_iff, internal_codedMoveTree_iff]
  exact tree_branch_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
    (codedMoveTree e T) (codedMoveTree_subtree e T hT) hW

end PolishSpaceBook.SetTheoryModels
