import Repair.FullIncrementNovOpenSourceModel
import Repair.FullIncrementNovOpenParameterNorms

/-! Actual transport from the internal source-slice model back to the
unchanged original Data.F, for the SAME displacement U.  The open equality
is used before taking the literal original within-line weighted atlas norm.
No smoothness outside parameterOpen, altered norm, or output estimate is
assumed.  Every order and every scale uses the same maps. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ey" => EuclideanSpace ℝ (Fin N)

omit [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
private theorem auxBridgeNov_original_open_weighted_coordinates
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) {c : ℕ}
    (f g : (Fin Data.atlas.count × Fin Data.parameterCount) →
      (Fin ((m+1)+d) → ℝ) → Fin c → ℝ)
    (hEq : ∀ i y, y ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i →
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).1 ∈ Data.parameterOpen →
      f i y = g i y)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell f
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) =
    paperAtlasWeighted base j ell g
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) := by
  let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart
  let W := fun i => O i ∩ (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹'
    incrementsOriginalParameterRegion Data
  have hO : ∀ i, IsOpen (O i) :=
    parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart
  have hW : ∀ i, IsOpen (W i) := fun i =>
    (parameterRound2_originalJointPoint_continuousOn Data.atlas Data.parameterChart i).isOpen_inter_preimage
      (hO i) (hd.parameter_open.prod isOpen_univ)
  have hSW : ∀ i, incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet i ⊆ W i := by
    intro i y hy
    exact ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩
  exact parameterRound2_paperWeighted_eq_of_open_germ f g O W _ hO hW
    (fun _ => inter_subset_left) hSW (fun i y hy => hEq i y hy.1 hy.2.1) base j ell

/-- The actual updated map in the internal model has exactly the original
updated map's weighted norm on the unchanged original evaluation domains. -/
theorem auxBridgeNov_open_update_map_weighted_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (U : P × M → Ey)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
        (fun z => fullIncrementNovOriginalSourceSlice Data z.1 z.2 + U z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) =
    paperAtlasWeighted base j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => Data.F z + U z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) := by
  apply auxBridgeNov_original_open_weighted_coordinates Data hd
  intro i y _ hp
  unfold incrementsOriginalMapCoordinates
  dsimp only
  rw [fullIncrementNov_original_source_slice_eq Data _ hp]

/-- The displacement from the ORIGINAL base map is the SAME U in every
original weighted norm, even if the internal model differs outside the
original open parameter region. -/
theorem auxBridgeNov_open_update_displacement_weighted_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (U : P × M → Ey)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
        (fun z => (fullIncrementNovOriginalSourceSlice Data z.1 z.2 + U z) - Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) =
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) := by
  apply auxBridgeNov_original_open_weighted_coordinates Data hd
  intro i y _ hp
  unfold incrementsOriginalMapCoordinates
  dsimp only
  rw [fullIncrementNov_original_source_slice_eq Data _ hp]
  simp only [add_sub_cancel_left]

/-- The literal source-only induced-metric error of the SAME U has equal
original weighted norms for the internal source-slice model and Data.F.
The equality covers all base orders, observation orders and scales. -/
theorem auxBridgeNov_open_metric_error_weighted_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (U : P × M → Ey) (delta : ℝ)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (incrementsOriginalMetricError
          (fun z => fullIncrementNovOriginalSourceSlice Data z.1 z.2) U Data.H delta))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) =
    paperAtlasWeighted base j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (incrementsOriginalMetricError Data.F U Data.H delta))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) := by
  apply auxBridgeNov_original_open_weighted_coordinates Data hd
  intro i y _ hp
  funext k
  unfold incrementsOriginalTensorCoordinates
  rw [← fullIncrementNov_original_metric_error_eq_open_source Data U delta _ hp]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.auxBridgeNov_open_update_map_weighted_eq
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_open_update_displacement_weighted_eq
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_open_metric_error_weighted_eq
