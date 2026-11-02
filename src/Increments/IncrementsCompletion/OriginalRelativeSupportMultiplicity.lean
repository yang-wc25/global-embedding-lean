import IncrementsCompletion.OriginalSupportMultiplicity

/-! The same original support-count argument for arbitrary original relative
support sets, restricted to the exact physical region that the caller uses. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation

theorem incrementsCompletion_original_label_support_count_of_hosts
    {X Host Label : Type*} [Fintype Host] [Fintype Label]
    (supports : Host → Set X) (degree basisCount : ℕ)
    (hDegree : ∀ a, tensorEnlargedSupportDegree supports a ≤ degree)
    (labelSupport : Label → Set X) (host : Label → Host) (slot : Label → Fin basisCount)
    (hLabel : Injective (fun nu => (host nu,slot nu))) (region : Set X)
    (hSupport : ∀ nu z, z ∈ region → z ∈ labelSupport nu → z ∈ supports (host nu)) :
    ∀ z ∈ region,
      (Finset.univ.filter (fun nu => z ∈ labelSupport nu)).card ≤ (degree+1)*basisCount := by
  intro z hz
  let active := Finset.univ.filter (fun nu => z ∈ labelSupport nu)
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
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_label_support_count_of_hosts
