import Probes.ActualIncrementOriginalOpenSlice
import Smoothing.ParameterRound2TensorGermTransfer

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-! The finite construction may use the actual smooth spatial totalization
of the original background. On every valid parameter its whole spatial
slice is the literal original background. The SAME U therefore has exactly
the original metric error in a neighborhood of every original sample. -/
theorem parameterRound2_metric_error_background_slice_eq
    (F0 F1 U : Ep × M → V)
    (H : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (delta : ℝ) (z : Ep × M)
    (hF : (fun x => F0 (z.1,x)) = (fun x => F1 (z.1,x))) :
    incrementsOriginalMetricError F0 U H delta z.1 z.2 =
      incrementsOriginalMetricError F1 U H delta z.1 z.2 := by
  have hAdd : (fun x => F0 (z.1,x)+U (z.1,x)) = (fun x => F1 (z.1,x)+U (z.1,x)) := by
    funext x
    rw [congrFun hF x]
  unfold incrementsOriginalMetricError
  rw [hAdd,hF]

theorem parameterRound2_metric_error_background_germ_transfer
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (H : parameterRound2_originalTensorGermSpace A B S W)
    (F0 F1 U : Ep × M → V) (delta : ℝ)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (hF : ∀ z ∈ G, (fun x => F0 (z.1,x)) = (fun x => F1 (z.1,x)))
    (hE : incrementsOriginalMetricError F0 U H.val delta ∈
      parameterRound2_originalTensorGermSpace A B S W) :
    incrementsOriginalMetricError F1 U H.val delta ∈
      parameterRound2_originalTensorGermSpace A B S W ∧
    ∀ base j scale, paperAtlasWeighted base j scale
      (incrementsOriginalTensorCoordinates A B (incrementsOriginalMetricError F1 U H.val delta))
      (incrementsOriginalDifferentiation A B) S =
      paperAtlasWeighted base j scale
        (incrementsOriginalTensorCoordinates A B (incrementsOriginalMetricError F0 U H.val delta))
        (incrementsOriginalDifferentiation A B) S := by
  have heq : ∀ z ∈ G, incrementsOriginalMetricError F0 U H.val delta z.1 z.2 =
      incrementsOriginalMetricError F1 U H.val delta z.1 z.2 :=
    fun z hz => parameterRound2_metric_error_background_slice_eq F0 F1 U H.val delta z (hF z hz)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO _ _ hE.1 G hG hSG heq
  · intro z hz
    exact ((inducedMetric_isPosSemidef (I := 𝓘(ℝ,D))
      (fun x => F1 (z.1,x)+U (z.1,x)) z.2).isSymm.sub
      (inducedMetric_isPosSemidef (I := 𝓘(ℝ,D)) (fun x => F1 (z.1,x)) z.2).isSymm).sub
      ((H.property.2 z hz).smul (delta^2))
  · intro base j scale
    exact parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO _ _ G hG hSG
      (fun z hz => (heq z hz).symm) base j scale

#print axioms parameterRound2_metric_error_background_slice_eq
#print axioms parameterRound2_metric_error_background_germ_transfer
end GlobalEmbedding.Continuation
