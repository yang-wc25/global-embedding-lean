import Probes.ActualSecondarySupportedSum

/-!
# Original secondary refinement multiplicity

A signed ordered primary pair may require several adapted charts. The true
secondary subordinate multiplicity is retained explicitly. The pointwise
count is at most `4 L² R`, where L is the active primary count and R the
active subordinate count for one signed pair. No total subordinate or atlas
cardinality enters the estimate.
-/

noncomputable section
open Set
open scoped Classical BigOperators
namespace GlobalEmbedding.Continuation

theorem actual_secondary_refined_active_card_le
    {Label Sub P : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
    (K : Label → Set P) (Ksub : ((Label × Label) × Fin 4) → Sub → Set P)
    (hsub : ∀ r a, Ksub r a ⊆ K r.1.1 ∩ K r.1.2)
    (x : P) (L R : ℕ)
    (hL : (Finset.univ.filter (fun nu => x ∈ K nu)).card ≤ L)
    (hR : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) →
      (Finset.univ.filter (fun a => x ∈ Ksub r a)).card ≤ R) :
    (Finset.univ.filter (fun t : (((Label × Label) × Fin 4) × Sub) =>
      (t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3) ∧ x ∈ Ksub t.1 t.2)).card ≤
      4 * L ^ 2 * R := by
  let active := Finset.univ.filter (fun r : (Label × Label) × Fin 4 =>
    (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) ∧ x ∈ K r.1.1 ∩ K r.1.2)
  let pieces := fun r : (Label × Label) × Fin 4 =>
    ({r} : Finset ((Label × Label) × Fin 4)).product
      (Finset.univ.filter (fun a => x ∈ Ksub r a))
  have ha : active.card ≤ 4 * L ^ 2 := actual_secondary_active_record_card_le K x L hL
  have hs : (Finset.univ.filter (fun t : (((Label × Label) × Fin 4) × Sub) =>
      (t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3) ∧ x ∈ Ksub t.1 t.2)) ⊆
      active.biUnion pieces := by
    intro t ht
    obtain ⟨hq, hx⟩ := (Finset.mem_filter.mp ht).2
    apply Finset.mem_biUnion.mpr
    refine ⟨t.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hsub t.1 t.2 hx⟩, ?_⟩
    exact Finset.mem_product.mpr ⟨by simp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hp : ∀ r ∈ active, (pieces r).card ≤ R := by
    intro r hr
    change (({r} : Finset ((Label × Label) × Fin 4)).product
      (Finset.univ.filter (fun a => x ∈ Ksub r a))).card ≤ R
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul]
    exact hR r (Finset.mem_filter.mp hr).2.1
  calc
    _ ≤ (active.biUnion pieces).card := Finset.card_le_card hs
    _ ≤ active.card * R := Finset.card_biUnion_le_card_mul active pieces R hp
    _ ≤ 4 * L ^ 2 * R := Nat.mul_le_mul_right R ha

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_refined_active_card_le
