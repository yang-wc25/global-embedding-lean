import Repair.ReferenceWeightedNativeData
import Repair.ReferenceOriginalLocalFactoryGlobal

/-! The actual primary multiplicity is controlled by the bounded proper
 labels. No total atlas count or total primary count enters this bound. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation

section Finite
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]

theorem increment_primary_support_card_le_label_bound
    (cutoff : ι → X → ℝ) (label : ι → ℕ) (labelBound : ℕ)
    (hBound : ∀ nu, label nu < labelBound)
    (hDistinct : ∀ nu mu, nu ≠ mu →
      (tsupport (cutoff nu) ∩ tsupport (cutoff mu)).Nonempty → label nu ≠ label mu)
    (z : X) :
    (Finset.univ.filter (fun nu => z ∈ tsupport (cutoff nu))).card ≤ labelBound := by
  let s := Finset.univ.filter (fun nu => z ∈ tsupport (cutoff nu))
  have hi : Set.InjOn label s := by
    intro nu hnu mu hmu he
    by_contra hne
    exact hDistinct nu mu hne ⟨z,(Finset.mem_filter.mp hnu).2,(Finset.mem_filter.mp hmu).2⟩ he
  have he : (s.image label).card = s.card := Finset.card_image_iff.mpr hi
  have hs : s.image label ⊆ Finset.range labelBound := by
    intro a ha
    obtain ⟨nu,hnu,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (hBound nu)
  calc
    s.card = (s.image label).card := he.symm
    _ ≤ (Finset.range labelBound).card := Finset.card_le_card hs
    _ = labelBound := Finset.card_range _
end Finite

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem increment_reference_primary_multiplicity
    (Data : IncrementsOriginalNativeData n d N M P)
    (label : Fin Data.primaryCount → ℕ) (labelBound : ℕ)
    (hBound : ∀ nu, label nu < labelBound)
    (hDistinct : ∀ nu mu, nu ≠ mu →
      (tsupport (Data.cutoff nu) ∩ tsupport (Data.cutoff mu)).Nonempty → label nu ≠ label mu)
    (weight : Fin Data.primaryCount → ℝ) :
    ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport ((repairReferenceWeightedData Data weight).cutoff nu))).card ≤
      labelBound :=
  increment_primary_support_card_le_label_bound Data.cutoff label labelBound hBound hDistinct

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_primary_support_card_le_label_bound
#print axioms GlobalEmbedding.Continuation.increment_reference_primary_multiplicity
