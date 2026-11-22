module

public import PolishSpaceBook.Determinacy
public import BorelDet.Proof.borel_determinacy
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Transport from Manthe's checked Borel-determinacy theorem

The imported development uses lists and legal extensions. The book uses finite
coordinate functions. The conversions below preserve the chosen move and every
compatible infinite play, including the distinction between the two players.
-/

namespace PolishSpaceBook
namespace MantheBridge
open GaleStewartGame Descriptive Tree
open scoped Stream'.Discrete MeasureTheory

abbrev fullTree : Descriptive.tree ℕ := ⊤

def game (A : Set (ℕ → ℕ)) : Game ℕ :=
  ⟨fullTree, {x | x.val ∈ A}⟩

/-- The imported branch subtype carries the usual Borel payoff. -/
theorem game_payoff_measurable {A : Set (ℕ → ℕ)} (hA : MeasurableSet A) :
    MeasurableSet[borel _] (game A).payoff := by
  have hB : MeasurableSet[borel (ℕ → ℕ)] A := by
    rwa [← BorelSpace.measurable_eq]
  exact hB.preimage continuous_subtype_val.borel_measurable

def toI (S : Strategy fullTree .zero) : BaireIStrategy := fun n s =>
  (S ⟨List.ofFn s, by trivial⟩ (by simp [IsPosition])).val

def toII (S : Strategy fullTree .one) : BaireIIStrategy := fun n s =>
  (S ⟨List.ofFn s, by trivial⟩ (by simp [IsPosition])).val

private theorem ofFn_prefix (x : ℕ → ℕ) (n : ℕ) :
    List.ofFn (fun i : Fin n => x i) = Stream'.take n x := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, Stream'.length_take]
  · intro i hi hj
    simp only [List.getElem_ofFn, Stream'.take_get, Stream'.get]

/-- Membership in a strategy tree is exactly agreement with its prescribed moves. -/
theorem mem_body_iff {p : Player} (S : Strategy fullTree p) (x : ℕ → ℕ) :
    x ∈ body S.pre.subtree ↔
      ∀ n (hp : IsPosition (Stream'.take n x) p),
        x n = (S ⟨Stream'.take n x, by trivial⟩ hp).val := by
  constructor
  · intro h n hp
    have hn := take_mem_body h (n + 1)
    have hs := hn.2 (y := Stream'.take n x) (a := x n)
      (by simpa only [← Stream'.concat_take_get, Stream'.get] using
        (List.prefix_rfl (l := Stream'.take (n + 1) x))) hp
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hs)
  · intro h y hx
    refine ⟨by trivial, ?_⟩
    intro z a hprefix hp
    have hz := Stream'.Discrete.principalOpen_mono hprefix hx
    obtain ⟨hz, ha⟩ := Stream'.Discrete.principalOpen_concat.mp hz
    have he := (Stream'.Discrete.principalOpen_iff_restrict x z).mp hz
    have hs := h z.length (by simpa only [← he] using hp)
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    apply ha.symm.trans
    exact hs.trans (Strategy.eval_val_congr S S rfl
      ⟨Stream'.take z.length x, by trivial⟩ ⟨z, by trivial⟩ (Subtype.ext he.symm) _)

theorem followsI_iff (S : Strategy fullTree .zero) (x : ℕ → ℕ) :
    BaireFollowsI (toI S) x ↔ x ∈ body S.pre.subtree := by
  rw [mem_body_iff]
  constructor
  · intro h n hp
    have hn : n = 2 * (n / 2) := by simp [IsPosition] at hp; omega
    have hh := h (n / 2)
    dsimp only [toI] at hh
    simp only [ofFn_prefix] at hh
    simpa only [← hn] using hh
  · intro h n
    simpa only [toI, ofFn_prefix] using h (2 * n) (by simp [IsPosition])

theorem followsII_iff (S : Strategy fullTree .one) (x : ℕ → ℕ) :
    BaireFollowsII (toII S) x ↔ x ∈ body S.pre.subtree := by
  rw [mem_body_iff]
  constructor
  · intro h n hp
    have hn : n = 2 * (n / 2) + 1 := by simp [IsPosition] at hp; omega
    have hh := h (n / 2)
    dsimp only [toII] at hh
    simp only [ofFn_prefix] at hh
    simpa only [← hn] using hh
  · intro h n
    simpa only [toII, ofFn_prefix] using h (2 * n + 1) (by simp [IsPosition])

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Strategy transport from the external game
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    Convert a history given as a function on a finite ordinal into the list of its values in increasing order.
    For Player I this list has length $2n$; for Player II it has length $2n+1$. Apply the imported strategy at this
    position and take its selected move. Every move is legal in the full tree. For an infinite play $x$, the list
    obtained from its first $m$ coordinates is exactly its length-$m$ prefix. Thus the equations saying that $x$
    follows the transported strategy are exactly the equations defining membership in the imported strategy tree.
-/
theorem determined {A : Set (ℕ → ℕ)} (h : (game A).IsDetermined) :
    BaireDetermined A := by
  obtain ⟨p, S, hS⟩ := h
  cases p with
  | zero =>
    refine Or.inl ⟨toI S, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hS ((followsI_iff S x).mp hx)
    exact hy
  | one =>
    refine Or.inr ⟨toII S, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hS ((followsII_iff S x).mp hx)
    exact hy

end MantheBridge

/-- Martin's theorem, imported with its proof and transported to the book's game. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{Borel determinacy}{Martin}] \emph{Every Borel subset of $\BaireSpace$ is
    determined.}
    \end{theorem*}
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    The payoff upstairs is the inverse image of $A$ under the map forgetting the proof of being a branch.
    This map is continuous, so a Borel $A$ gives a Borel payoff. The imported theorem supplies a winning strategy;
    the equality of compatible plays transfers its winning property to $G_A$.
-/
theorem baire_borel_determined {A : Set (ℕ → ℕ)} (hA : MeasurableSet A) :
    BaireDetermined A := by
  apply MantheBridge.determined
  exact GaleStewartGame.borel_determinacy (MantheBridge.game_payoff_measurable hA)
    Descriptive.Tree.top_isPruned

end PolishSpaceBook
