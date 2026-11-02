import Repair.IncrementGivenPhaseTransitions
import GlobalEmbedding.Offline.ParametricPhaseStability

/-! Spatial transition derivatives are the actual source slices of the
original product transition. Restriction to source directions costs at
most one. Order zero is supplied separately by the original coordinate
radius; no zero-order parameter transition bound is required. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

def repairOriginalSpatialFullProfile (B : ℝ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then B else Spatial j

theorem repairOriginalSpatialFullProfile_nonneg (B : ℝ) (Spatial : ℕ → ℝ)
    (hB : 0 ≤ B) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ repairOriginalSpatialFullProfile B Spatial j := by
  unfold repairOriginalSpatialFullProfile
  split_ifs
  · exact hB
  · exact hSpatial j

theorem repair_original_spatial_transition_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i k : Fin Data.atlas.count) (x : D) (hx : x ∈ Data.sourceNormDomain i)
    (hOverlap : x ∈ ((Data.atlas.chart i).symm.trans (Data.atlas.chart k)).source)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (Data.atlas.chart k ∘ (Data.atlas.chart i).symm) x‖ ≤ Spatial j := by
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i) (Data.atlas.chart k)
  let u : Ep × D → D := fun z => (S z).2
  have hS := (repair_reference_host_transition_smooth («Ep» := Ep)
    (Data.atlas.chart i) (Data.atlas.chart k) (hd.atlas_smooth.chart_mem i) (hd.atlas_smooth.chart_mem k)).1
  have hz : ((0 : Ep),x) ∈ S.source := ⟨mem_univ _,hOverlap⟩
  have hu : ContDiffOn ℝ ∞ u S.source := hS.snd
  have hSlice := norm_iteratedFDeriv_source_slice_le S.open_source hu j hz
  have hProj := (ContinuousLinearMap.snd ℝ Ep D).norm_iteratedFDeriv_comp_left
    (hS.contDiffAt (S.open_source.mem_nhds hz)) (n := j) (by simp)
  have hNative := transition.spatial i k j hj (0,x) hx hz
  exact hSlice.trans (hProj.trans
    ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hNative))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_spatial_transition_jets
