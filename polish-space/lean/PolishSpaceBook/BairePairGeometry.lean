module

public import PolishSpaceBook.PairTreeGeometry

@[expose] public section

/-!
# Coordinatewise codes for pairs of Baire reals

Natural-number pairing combines the point and witness coordinates. The
finite-word operations commute with taking the prefixes used by tree codes.
-/

namespace PolishSpaceBook

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \forward{NamePair,NameProjection}
      \define{WordPair}
    \end{mathmeta}
    For sequences, use pointwise numerical pairing
    $\NamePair{p}{q}(n)=\NatPair{p(n)}{q(n)}$, and let $\NameProjection{1}{u}$ and
    $\NameProjection{2}{u}$ apply the two numerical inverse projections to every entry of $u$.
    They recover $p,q$ from their pair, and pairing the two projections recovers $u$.
    For finite words, $\WordPair{s}{t}$ has length $|s|$ and pairs their entries in order, using zero for
    an entry of $t$ beyond its length. On equal-length words, no default is needed. Pairing and both
    projections commute with taking equal-length prefixes.
-/
def pairBaire (x y : ℕ → ℕ) : ℕ → ℕ := fun n => Nat.pair (x n) (y n)
def leftBaire (p : ℕ → ℕ) : ℕ → ℕ := fun n => (p n).unpair.1
def rightBaire (p : ℕ → ℕ) : ℕ → ℕ := fun n => (p n).unpair.2

@[simp] theorem leftBaire_pair (x y : ℕ → ℕ) : leftBaire (pairBaire x y) = x := by
  funext n
  simp [leftBaire, pairBaire]

@[simp] theorem rightBaire_pair (x y : ℕ → ℕ) : rightBaire (pairBaire x y) = y := by
  funext n
  simp [rightBaire, pairBaire]

@[simp] theorem pairBaire_left_right (p : ℕ → ℕ) : pairBaire (leftBaire p) (rightBaire p) = p := by
  funext n
  simp [pairBaire, leftBaire, rightBaire]

/-- Pair words of equal length. The default is relevant only on unequal
length inputs; the tree constructions test synchronized prefixes. -/
def pairWords (s t : finseq ℕ) : finseq ℕ :=
  (List.range s.length).map (fun i => Nat.pair (s.getD i 0) (t.getD i 0))

@[simp] theorem leftWitness_prefix (p : ℕ → ℕ) (n : ℕ) :
    leftWitness (seqPrefix p n) = seqPrefix (leftBaire p) n := by
  simp [leftWitness, seqPrefix, leftBaire, List.map_ofFn, Function.comp_def]

@[simp] theorem rightWitness_prefix (p : ℕ → ℕ) (n : ℕ) :
    rightWitness (seqPrefix p n) = seqPrefix (rightBaire p) n := by
  simp [rightWitness, seqPrefix, rightBaire, List.map_ofFn, Function.comp_def]

@[simp] theorem pairWords_prefix (x y : ℕ → ℕ) (n : ℕ) :
    pairWords (seqPrefix x n) (seqPrefix y n) = seqPrefix (pairBaire x y) n := by
  apply List.ext_getElem
  · simp [pairWords, seqPrefix_length]
  · intro i hi hi'
    have hin : i < n := by simpa [seqPrefix_length] using hi'
    simp [pairWords, seqPrefix, pairBaire, hin, List.getD_eq_getElem?_getD]

end PolishSpaceBook
