module

public import Mathlib.ModelTheory.Fraisse

@[expose] public section

/-! # Finite simultaneous chart amalgamation

Realize finitely many embedding requests over one structure using amalgamation.
No hereditary closure of the class is assumed.
-/

namespace PolishSpaceBook.ChartAmalgamation

open FirstOrder FirstOrder.Language CategoryTheory

universe u v w

variable {L : Language.{u, v}} {K : Set (Bundled.{w} L.Structure)}
variable (hap : Amalgamation K)
variable {I : Type*} (A B : I → Bundled.{w} L.Structure)
variable (h : ∀ r, A r ↪[L] B r)

include hap

/-- Amalgamation realizes any finite family of requests over a common base.
The base embedding is shared by every resulting commuting triangle. -/
theorem finite_requests (s : Finset I) (M : Bundled.{w} L.Structure) (hM : M ∈ K)
    (e : ∀ r, A r ↪[L] M)
    (hA : ∀ r ∈ s, A r ∈ K) (hB : ∀ r ∈ s, B r ∈ K) :
    ∃ (Q : Bundled.{w} L.Structure) (i : M ↪[L] Q),
      Q ∈ K ∧ ∀ r ∈ s, ∃ g : B r ↪[L] Q, g.comp (h r) = i.comp (e r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, Embedding.refl L M, hM, by simp⟩
  | @insert r s hrs ih =>
      obtain ⟨Q, i, hQ, hi⟩ := ih
        (fun t ht => hA t (Finset.mem_insert_of_mem ht))
        (fun t ht => hB t (Finset.mem_insert_of_mem ht))
      obtain ⟨R, j, g, hR, hj⟩ := hap (A r) Q (B r) (i.comp (e r)) (h r)
        (hA r (Finset.mem_insert_self r s)) hQ (hB r (Finset.mem_insert_self r s))
      refine ⟨R, j.comp i, hR, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · refine ⟨g, ?_⟩
        exact hj.symm
      · obtain ⟨g', hg'⟩ := hi t ht
        refine ⟨j.comp g', ?_⟩
        change j.comp (g'.comp (h t)) = j.comp (i.comp (e t))
        rw [hg']

omit hap in
/-- Embeddings between finite carriers form a finite type, regardless of the
cardinality of the relation-symbol set. -/
theorem finite_embeddings (M N : Bundled.{w} L.Structure) [Finite M] [Finite N] :
    Finite (M ↪[L] N) :=
  Finite.of_injective (fun f : M ↪[L] N => (f : M → N)) DFunLike.coe_injective

/-- One stage meets every request between the first finitely many charts.
Both the donor embedding and the map into the current chart are quantified. -/
theorem bounded_requests (C : ℕ → Bundled.{w} L.Structure)
    (hC : ∀ n, C n ∈ K) [∀ n, Finite (C n)]
    (n : ℕ) (M : Bundled.{w} L.Structure) [Finite M] (hM : M ∈ K) :
    ∃ (Q : Bundled.{w} L.Structure) (i : M ↪[L] Q), Q ∈ K ∧
      ∀ (a b : Fin (n + 1)) (h : C a ↪[L] C b) (e : C a ↪[L] M),
        ∃ g : C b ↪[L] Q, g.comp h = i.comp e := by
  classical
  let R := Σ a : Fin (n + 1), Σ b : Fin (n + 1),
    (C a ↪[L] C b) × (C a ↪[L] M)
  let : ∀ a b : Fin (n + 1), Fintype (C a ↪[L] C b) := fun a b =>
    @Fintype.ofFinite _ (finite_embeddings (C a) (C b))
  let : ∀ a : Fin (n + 1), Fintype (C a ↪[L] M) := fun a =>
    @Fintype.ofFinite _ (finite_embeddings (C a) M)
  let : Fintype R := by dsimp [R]; infer_instance
  obtain ⟨Q, i, hQ, hi⟩ := finite_requests hap
    (fun r : R => C r.1) (fun r : R => C r.2.1)
    (fun r : R => r.2.2.1) Finset.univ M hM
    (fun r : R => r.2.2.2) (fun r _ => hC r.1) (fun r _ => hC r.2.1)
  exact ⟨Q, i, hQ, fun a b h e => hi ⟨a, b, h, e⟩ (Finset.mem_univ _)⟩

/-- Iterate bounded amalgamation. The chain and its one-step embeddings are
constructed here; an extension property for a pre-existing limit is not assumed. -/
theorem exists_request_chain (C : ℕ → Bundled.{w} L.Structure)
    (hC : ∀ n, C n ∈ K) (hfin : ∀ M ∈ K, Finite M) :
    ∃ (G : ℕ → {M : Bundled.{w} L.Structure // M ∈ K})
      (f : ∀ n, (G n).val ↪[L] (G (n + 1)).val),
      ∀ (n : ℕ) (a b : Fin (n + 1))
        (h : C a ↪[L] C b) (e : C a ↪[L] (G n).val),
        ∃ g : C b ↪[L] (G (n + 1)).val, g.comp h = (f n).comp e := by
  classical
  let : ∀ n, Finite (C n) := fun n => hfin (C n) (hC n)
  have step (n : ℕ) (M : {M : Bundled.{w} L.Structure // M ∈ K}) :
      ∃ (N : {M : Bundled.{w} L.Structure // M ∈ K}) (i : M.val ↪[L] N.val),
        ∀ (a b : Fin (n + 1)) (h : C a ↪[L] C b) (e : C a ↪[L] M.val),
          ∃ g : C b ↪[L] N.val, g.comp h = i.comp e := by
    let : Finite M.val := hfin M.val M.property
    obtain ⟨Q, i, hQ, hi⟩ := bounded_requests hap C hC n M.val M.property
    exact ⟨⟨Q, hQ⟩, i, hi⟩
  choose next edge hedge using step
  let G : ℕ → {M : Bundled.{w} L.Structure // M ∈ K} :=
    fun n => Nat.rec ⟨C 0, hC 0⟩ (fun k M => next k M) n
  refine ⟨G, fun n => edge n (G n), ?_⟩
  exact fun n => hedge n (G n)

omit hap in
/-- Every embedding of a finite structure into a chain limit factors through
one stage, as a structure embedding rather than only a map of carriers. -/
theorem embedding_factors {G : ℕ → Type w} [∀ n, L.Structure (G n)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (M : Type w) [L.Structure M] [Finite M] (e : M ↪[L] Language.DirectLimit G f) :
    ∃ (n : ℕ) (g : M ↪[L] G n), (DirectLimit.of L ℕ G f n).comp g = e := by
  obtain ⟨n, y, hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq G f (e : M → _)
  let q := DirectLimit.of L ℕ G f n
  have hp (x : M) : q (y x) = e x := (congrFun hy x).symm
  let g : M ↪[L] G n := {
    toFun := y
    inj' := fun x z hxz => e.injective (by rw [← hp x, ← hp z, hxz])
    map_fun' := fun F x => q.injective (by
      rw [hp, q.map_fun]
      simpa only [Function.comp_def, hp] using e.map_fun F x)
    map_rel' := fun R x => by
      have hq := q.map_rel R (y ∘ x)
      have he := e.map_rel R x
      simp only [Function.comp_def, hp] at hq he
      exact hq.symm.trans he }
  exact ⟨n, g, by ext x; exact hp x⟩

omit hap in
/-- Bounded requests along a chain give the extension property in its limit. -/
theorem limit_extension (C : ℕ → Bundled.{w} L.Structure)
    [∀ n, Finite (C n)] {G : ℕ → Type w} [∀ n, L.Structure (G n)]
    (f : ∀ n, G n ↪[L] G (n + 1))
    (hs : ∀ (n : ℕ) (a b : Fin (n + 1))
      (h : C a ↪[L] C b) (e : C a ↪[L] G n),
      ∃ g : C b ↪[L] G (n + 1), g.comp h = (f n).comp e)
    (a b : ℕ) (h : C a ↪[L] C b)
    (e : C a ↪[L] Language.DirectLimit G (DirectedSystem.natLERec f)) :
    ∃ g : C b ↪[L] Language.DirectLimit G (DirectedSystem.natLERec f), g.comp h = e := by
  let F := DirectedSystem.natLERec f
  obtain ⟨k, e₀, he₀⟩ := embedding_factors F (C a) e
  let n := max k (max a b)
  have hk : k ≤ n := le_max_left _ _
  have ha : a < n + 1 := Nat.lt_succ_of_le ((le_max_left a b).trans (le_max_right k _))
  have hb : b < n + 1 := Nat.lt_succ_of_le ((le_max_right a b).trans (le_max_right k _))
  obtain ⟨g, hg⟩ := hs n ⟨a, ha⟩ ⟨b, hb⟩ h ((F k n hk).comp e₀)
  refine ⟨(DirectLimit.of L ℕ G F (n + 1)).comp g, ?_⟩
  ext x
  have hstep (z : G n) :
      DirectLimit.of L ℕ G F (n + 1) (f n z) = DirectLimit.of L ℕ G F n z := by
    have hF : F n (n + 1) (Nat.le_succ n) = f n := by
      simp only [F, DirectedSystem.natLERec, Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
      rfl
    simpa only [hF] using
      (DirectLimit.of_f (f := F) (hij := Nat.le_succ n) (x := z))
  change DirectLimit.of L ℕ G F (n + 1) (g (h x)) = e x
  have hgx : g (h x) = f n (F k n hk (e₀ x)) := DFunLike.congr_fun hg x
  rw [hgx, hstep]
  rw [DirectLimit.of_f]
  exact DFunLike.congr_fun he₀ x

omit hap in
/-- Joint embedding and extension over representatives imply universality,
provided at least one class member already embeds in the structure. -/
theorem universal_of_extension (hjep : JointEmbedding K)
    (C : ℕ → Bundled.{w} L.Structure)
    (hcover : ∀ Q ∈ K, ∃ n, Nonempty (Q ≃[L] C n))
    (M : Type w) [L.Structure M]
    (hext : ∀ a b (h : C a ↪[L] C b) (e : C a ↪[L] M),
      ∃ g : C b ↪[L] M, g.comp h = e)
    (S : Bundled.{w} L.Structure) (hS : S ∈ K) (eS : S ↪[L] M)
    (B : Bundled.{w} L.Structure) (hB : B ∈ K) : Nonempty (B ↪[L] M) := by
  obtain ⟨a, ⟨ea⟩⟩ := hcover S hS
  obtain ⟨Q, hQ, ⟨i⟩, ⟨j⟩⟩ := hjep S hS B hB
  obtain ⟨b, ⟨eb⟩⟩ := hcover Q hQ
  obtain ⟨g, _⟩ := hext a b
    (eb.toEmbedding.comp (i.comp ea.symm.toEmbedding)) (eS.comp ea.symm.toEmbedding)
  exact ⟨g.comp (eb.toEmbedding.comp j)⟩

omit hap in
/-- Transport the extension property from representatives to every class member. -/
theorem extension_of_representatives (C : ℕ → Bundled.{w} L.Structure)
    (hcover : ∀ Q ∈ K, ∃ n, Nonempty (Q ≃[L] C n))
    (M : Type w) [L.Structure M]
    (hext : ∀ a b (h : C a ↪[L] C b) (e : C a ↪[L] M),
      ∃ g : C b ↪[L] M, g.comp h = e)
    (A B : Bundled.{w} L.Structure) (hA : A ∈ K) (hB : B ∈ K)
    (h : A ↪[L] B) (e : A ↪[L] M) :
    ∃ g : B ↪[L] M, g.comp h = e := by
  obtain ⟨a, ⟨ea⟩⟩ := hcover A hA
  obtain ⟨b, ⟨eb⟩⟩ := hcover B hB
  obtain ⟨g, hg⟩ := hext a b
    (eb.toEmbedding.comp (h.comp ea.symm.toEmbedding)) (e.comp ea.symm.toEmbedding)
  refine ⟨g.comp eb.toEmbedding, ?_⟩
  ext x
  have hx := DFunLike.congr_fun hg (ea x)
  change g (eb (h (ea.symm (ea x)))) = e (ea.symm (ea x)) at hx
  change g (eb (h x)) = e x
  simpa only [ea.symm_apply_apply] using hx

/-- Construct a countable universal structure with extension over all class
members, using amalgamation and joint embedding only. -/
theorem exists_countable_universal_extension (hjep : JointEmbedding K)
    (C : ℕ → Bundled.{w} L.Structure) (hC : ∀ n, C n ∈ K)
    (hfin : ∀ Q ∈ K, Finite Q)
    (hcover : ∀ Q ∈ K, ∃ n, Nonempty (Q ≃[L] C n)) :
    ∃ M : Bundled.{w} L.Structure, Countable M ∧
      (∀ Q ∈ K, Nonempty (Q ↪[L] M)) ∧
      (∀ A B : Bundled.{w} L.Structure, A ∈ K → B ∈ K →
        ∀ (h : A ↪[L] B) (e : A ↪[L] M), ∃ g : B ↪[L] M, g.comp h = e) ∧
      (∀ k (x : Fin k → M), ∃ (Q : Bundled.{w} L.Structure) (_ : Q ∈ K)
        (i : Q ↪[L] M) (y : Fin k → Q), ∀ t, i (y t) = x t) := by
  classical
  obtain ⟨G, f, hs⟩ := exists_request_chain hap C hC hfin
  let : ∀ n, Finite (G n).val := fun n => hfin (G n).val (G n).property
  let : ∀ n, Finite (C n) := fun n => hfin (C n) (hC n)
  let F := DirectedSystem.natLERec f
  let M := Language.DirectLimit (fun n => (G n).val) F
  have hext := limit_extension C f hs
  have hcount : Countable M := by
    dsimp [M, Language.DirectLimit]
    infer_instance
  refine ⟨Bundled.of M, hcount, ?_, extension_of_representatives C hcover M hext, ?_⟩
  · intro Q hQ
    exact universal_of_extension hjep C hcover M hext (G 0).val (G 0).property
      (DirectLimit.of L ℕ (fun n => (G n).val) F 0) Q hQ
  · intro k x
    obtain ⟨n, y, hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
      (fun n => (G n).val) F x
    exact ⟨(G n).val, (G n).property, DirectLimit.of L ℕ (fun n => (G n).val) F n,
      y, fun t => (congrFun hy t).symm⟩

end PolishSpaceBook.ChartAmalgamation
