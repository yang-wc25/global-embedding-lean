import Probes.ActualIncrementOriginalOpenSlice
import Probes.ActualIncrementReserveAdmissibility

/-! The original immersion and coordinate ellipticity supply the true
qualitative injectivity domain and the genuine sampled first-frame reserve.
Every valid parameter is exactly the original F slice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)

theorem actual_original_open_slice_first_injective
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (hImm : IncrementsOriginalSliceImmersionInputs D)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ∀ z ∈ actualOriginalNativeOpen D i, Function.Injective
      (fderiv ℝ (actualOriginalOpenParameterSlice D i z.1 ∘ (D.atlas.chart i.1).symm) z.2) := by
  intro z hz
  let F := actualOriginalOpenParameterSlice D i z.1
  have hF := actualOriginalOpenParameterSlice_contMDiff D hd hs i z.1
  have ht := actualOriginalNativeMap_source_target D i hz.1
  have hm : Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) F ((D.atlas.chart i.1).symm z.2)) := by
    change Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (actualOriginalOpenParameterSlice D i z.1) _)
    rw [actualOriginalOpenParameterSlice_eq D i z.1 (actualOriginalNativeOpen_parameter D i hz)]
    exact hImm.immersion _ (actualOriginalNativeOpen_parameter D i hz) _
  rw [actual_increment_coordinate_first_derivative_eq F hF (D.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) z.2 ht]
  let C1 := actualIncrementChartDerivativeEquiv (D.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) z.2 ht
  exact ((tangentSpaceCastModel 𝓘(ℝ,V) (F ((D.atlas.chart i.1).symm z.2))).injective.comp hm).comp
    C1.injective

theorem actual_original_open_slice_coordinate_ellipticity
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs D c)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {z : X} (hz : parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i) :
    ∀ v : Es, c*‖v‖^2 ≤ ‖fderiv ℝ
      (actualOriginalOpenParameterSlice D i z.1 ∘ (D.atlas.chart i.1).symm) z.2 v‖^2 := by
  obtain ⟨hx,hp⟩ := actualOriginalNativeMap_evaluation_members D i hz
  rw [actualOriginalOpenParameterSlice_eq D i z.1 (hd.parameter_subset hp)]
  exact hEll.lower _ hp i.1 z.2 hx

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_open_slice_first_injective
#print axioms GlobalEmbedding.Continuation.actual_original_open_slice_coordinate_ellipticity
