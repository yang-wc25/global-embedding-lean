import Probes.ActualIncrementOriginalMeanPrimitives
import Smoothing.ParameterRound2MeanRawGermReserveSupply
import Smoothing.ParameterRound2OriginalGermReserveBall

/-! Identity parameter charts retain the exact native Euclidean tensor
carrier used by finite mean iteration. These identities do not require the
parameter set to be all of Euclidean space or to have dimension zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × Es

theorem parameterRound2_identity_parameter_tensor_slice
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)) :
    actualOriginalParameterTensorSlice Data i input = input := by
  funext p x
  simp only [actualOriginalParameterTensorSlice,hId,OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply,id_eq]

theorem parameterRound2_identity_parameter_neighborhood
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (ip : Fin Data.parameterCount)
    (hId : Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (G : Set (Ep × M)) : actualOriginalParameterNeighborhood Data ip G = G := by
  ext z
  simp [actualOriginalParameterNeighborhood,hId]

theorem parameterRound2_identity_parameter_map :
    parameterRound2_meanParameterMap (m := m) (OpenPartialHomeomorph.refl Ep) = id := by
  funext z
  rfl

theorem parameterRound2_identity_parameter_sample_image
    (B : OpenPartialHomeomorph Ep Ep) (hB : B = OpenPartialHomeomorph.refl Ep)
    (S : Set (Fin (m+1+d) → ℝ)) :
    parameterRound2_meanParameterMap (m := m) B ''
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S) =
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S) := by
  rw [hB,parameterRound2_identity_parameter_map,image_id]

#print axioms parameterRound2_identity_parameter_tensor_slice
#print axioms parameterRound2_identity_parameter_neighborhood
#print axioms parameterRound2_identity_parameter_sample_image
end GlobalEmbedding.Continuation
