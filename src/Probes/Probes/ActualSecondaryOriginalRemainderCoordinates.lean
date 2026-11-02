import Probes.ActualSecondaryRawMetricData
import Probes.ActualSecondaryTotalMetricCoordinates
import Smoothing.ParameterRound2MeanRawNative

/-! Exact original tensor coordinates of the same constructed increment after
subtracting its same native mean. The actual inverse parameter chart is kept
inside the function before joint differentiation. No global regularity of U
or additional residual identity is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff Classical
namespace GlobalEmbedding.Continuation
variable {m d N pcount : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_original_metric_sub_mean_defect
    (F U : Ep × M → V)
    (H Mean : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (delta : ℝ) :
    (fun p x => incrementsOriginalMetricError F U H delta p x-delta^2 • (Mean p x-H p x)) =
      incrementsOriginalMetricError F U Mean delta := by
  funext p x
  ext v w
  simp only [incrementsOriginalMetricError,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  ring

 theorem actual_original_mean_removed_native_pullback
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (i : Fin A.count × Fin pcount) :
    EqOn (actualOriginalNativeTargetTensor A B
      (incrementsOriginalMetricError (fun y => F y.1 y.2)
        (actualOriginalIncrementMap F hF g input length tau delta choice)
        (incrementsGlobalPrimaryMean F hF g input length tau) delta) i)
      (actualOriginalMeanRemovedMetric F hF g input length tau delta choice (A.chart i.1) ∘
        parameterRound2_meanParameterMap (m := m) (B i.2))
      ((B i.2).target ×ˢ (A.chart i.1).target) := by
  intro z hz
  rw [actual_original_native_metric_error_pullback_total A B hA]
  · have hMean : actualOriginalNativeTargetTensor A B
        (incrementsGlobalPrimaryMean F hF g input length tau) i z =
        actualRealTensorAssembly (fun a b =>
          (incrementsGlobalPrimaryMean F hF g input length tau ((B i.2).symm z.1) ((A.chart i.1).symm z.2)
            (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 a)
            (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 b) : ℂ)) := by
      apply actual_bilinear_tensor_eq_of_basis
      intro a b
      rw [actualOriginalNativeTargetTensor_basis,actualRealTensorAssembly_basis,Complex.ofReal_re]
    simp only [actualOriginalNativeMetricError,actualFiniteMetricError,
      Function.comp_apply,actualOriginalMeanRemovedMetric,actualOriginalObservedMeanTensor,
      parameterRound2_meanParameterMap,smul_zero,sub_zero]
    rw [hMean]
    ext v w
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.zero_apply,smul_eq_mul,mul_zero,sub_zero]
  · exact hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_mean_removed_native_pullback
