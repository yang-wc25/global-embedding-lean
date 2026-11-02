import Probes.Round4PrimaryLocalMultiplicity

/-! Original local support multiplicity from the enlarged-support graph and
bounded labels per host. No actual cutoff, primary domain or norm is modified.
The point set may be the original evaluation region; outside extensions need
not satisfy the support relation. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation

theorem incrementsCompletion_original_hosts_through_point
    {X Host : Type*} [Fintype Host]
    (supports : Host → Set X) (degree : ℕ)
    (hDegree : ∀ a, tensorEnlargedSupportDegree supports a ≤ degree) (z : X) :
    (Finset.univ.filter (fun a => z ∈ supports a)).card ≤ degree+1 := by
  let active := Finset.univ.filter (fun a => z ∈ supports a)
  by_cases he : active = ∅
  · simp only [show Finset.univ.filter (fun a => z ∈ supports a) = ∅ from he,
      Finset.card_empty]
    omega
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let graph := tensorEnlargedSupportGraph supports
  have hsub : active ⊆ insert a (graph.neighborFinset a) := by
    intro b hb
    by_cases hba : b = a
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · exact Finset.mem_insert.mpr (Or.inr ((graph.mem_neighborFinset a b).mpr
        ⟨Ne.symm hba,z,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩))
  calc
    active.card ≤ (insert a (graph.neighborFinset a)).card := Finset.card_le_card hsub
    _ ≤ (graph.neighborFinset a).card+1 := Finset.card_insert_le _ _
    _ ≤ degree+1 := Nat.add_le_add_right (hDegree a) 1

theorem incrementsCompletion_original_cutoff_count_of_hosts
    {X Host Label : Type*} [TopologicalSpace X] [Fintype Host] [Fintype Label]
    (supports : Host → Set X) (degree basisCount : ℕ)
    (hDegree : ∀ a, tensorEnlargedSupportDegree supports a ≤ degree)
    (chi : Label → X → ℝ) (host : Label → Host) (slot : Label → Fin basisCount)
    (hLabel : Injective (fun nu => (host nu,slot nu))) (region : Set X)
    (hSupport : ∀ nu z, z ∈ region → z ∈ tsupport (chi nu) → z ∈ supports (host nu)) :
    ∀ z ∈ region,
      (Finset.univ.filter (fun nu => z ∈ tsupport (chi nu))).card ≤ (degree+1)*basisCount := by
  intro z hz
  let active := Finset.univ.filter (fun nu => z ∈ tsupport (chi nu))
  let hosts := Finset.univ.filter (fun a => z ∈ supports a)
  let target := hosts.product (Finset.univ : Finset (Fin basisCount))
  have hcount : active.card ≤ target.card := Finset.card_le_card_of_injOn
    (fun nu => (host nu,slot nu)) (by
      intro nu hnu
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hSupport nu z hz (Finset.mem_filter.mp hnu).2⟩,
          Finset.mem_univ _⟩)
    (fun _ _ _ _ h => hLabel h)
  calc
    active.card ≤ target.card := hcount
    _ = hosts.card*basisCount := by simp [target]
    _ ≤ (degree+1)*basisCount := Nat.mul_le_mul_right basisCount
      (incrementsCompletion_original_hosts_through_point supports degree hDegree z)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_hosts_through_point
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_cutoff_count_of_hosts
