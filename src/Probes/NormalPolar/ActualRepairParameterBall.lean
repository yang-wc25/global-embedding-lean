import Smoothing.TensorLocalModelDomains

/-!
# An actual parameter ball inside the fixed repair sampling domains

An arbitrary chart need not send the chosen parameter to zero, and the
Euclidean and Pi norms are not isometric.  The map below keeps the actual
chart centre and uses the true norm of the coordinate equivalence to select
a positive Pi-norm ball.  Its coordinate image lies in the already fixed
sampling set.  This radius depends only on fixed chart data, before the
scale, probe parameters, or repair trajectory are chosen.
-/

noncomputable section
open Set Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {d : ℕ} {ι P : Type*} [Fintype ι]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Fin d → ℝ

def actualRepairParameterRadius (B : TensorBufferedChartFamily ι P Ep) : ℝ :=
  B.buffer / (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ + 1)

theorem actualRepairParameterRadius_pos (B : TensorBufferedChartFamily ι P Ep) :
    0 < actualRepairParameterRadius B := by
  exact div_pos B.buffer_pos (by positivity)

def actualRepairParameterMap (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ : P) (u : X) : P :=
  (B.chart b).symm (B.chart b p₀ + (EuclideanSpace.equiv (Fin d) ℝ).symm u)

theorem actualRepairParameter_coordinates_mem_sampling
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (hp₀ : p₀ ∈ B.inner b) (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    B.chart b p₀ + (EuclideanSpace.equiv (Fin d) ℝ).symm u ∈
      tensorLocalSamplingCoordinates B b := by
  apply mem_iUnion.mpr
  refine ⟨B.chart b p₀, mem_iUnion.mpr ⟨tensorLocalInner_mem B b hp₀, ?_⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
  let C := ‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hbound : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm u‖ ≤ C * ‖u‖ :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.le_opNorm u
  have hsmall : (C + 1) * ‖u‖ < B.buffer := by
    have h := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hu
    simpa only [mul_comm] using h
  exact (hbound.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
    (norm_nonneg u))).trans_lt hsmall

theorem actualRepairParameter_coordinates_mem_fixed_sample
    (B : TensorBufferedChartFamily ι P Ep) (Q : ι → Set Ep)
    (hQ : ∀ b, tensorLocalSamplingCoordinates B b ⊆ Q b)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    B.chart b p₀ + (EuclideanSpace.equiv (Fin d) ℝ).symm u ∈ Q b :=
  hQ b (actualRepairParameter_coordinates_mem_sampling B b p₀ hp₀ u hu)

theorem actualRepairParameter_coordinates_mem_target
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (hp₀ : p₀ ∈ B.inner b) (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    B.chart b p₀ + (EuclideanSpace.equiv (Fin d) ℝ).symm u ∈ (B.chart b).target :=
  tensorLocalSampling_subset_target B b
    (actualRepairParameter_coordinates_mem_sampling B b p₀ hp₀ u hu)

theorem actualRepairParameterMap_zero
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    actualRepairParameterMap B b p₀ 0 = p₀ := by
  simp only [actualRepairParameterMap, map_zero, add_zero]
  exact (B.chart b).left_inv (B.inner_subset b hp₀)

theorem actualRepairParameterMap_coordinates
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (hp₀ : p₀ ∈ B.inner b) (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b (actualRepairParameterMap B b p₀ u)) =
      (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀) + u := by
  unfold actualRepairParameterMap
  rw [(B.chart b).right_inv (actualRepairParameter_coordinates_mem_target B b p₀ hp₀ u hu),
    map_add, ContinuousLinearEquiv.apply_symm_apply]

theorem actualRepairParameterMap_smooth
    (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ContMDiffOn 𝓘(ℝ, X) 𝓘(ℝ, Ep) ∞ (actualRepairParameterMap B b p₀)
      (Metric.ball 0 (actualRepairParameterRadius B)) := by
  have hAffine : ContMDiff 𝓘(ℝ, X) 𝓘(ℝ, Ep) ∞
      (fun u : X ↦ B.chart b p₀ + (EuclideanSpace.equiv (Fin d) ℝ).symm u) :=
    (contDiff_const.add (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff).contMDiff
  exact (contMDiffOn_symm_of_mem_maximalAtlas (hB b)).comp hAffine.contMDiffOn
    (fun u hu ↦ actualRepairParameter_coordinates_mem_target B b p₀ hp₀ u
      (by simpa only [Metric.mem_ball, dist_zero_right] using hu))

/-- The actual chart coordinates have the identity parameter derivative.
The translation is retained, and the equality is proved on an open ball. -/
theorem actualRepairParameterMap_coordinate_derivative
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (hp₀ : p₀ ∈ B.inner b) (u a : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    fderiv ℝ (fun v : X ↦ (EuclideanSpace.equiv (Fin d) ℝ)
      (B.chart b (actualRepairParameterMap B b p₀ v))) u a = a := by
  have heq : (fun v : X ↦ (EuclideanSpace.equiv (Fin d) ℝ)
      (B.chart b (actualRepairParameterMap B b p₀ v))) =ᶠ[𝓝 u]
      (fun v : X ↦ (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀) + v) := by
    have hub : u ∈ Metric.ball (0 : X) (actualRepairParameterRadius B) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    filter_upwards [Metric.isOpen_ball.mem_nhds hub] with v hv
    exact actualRepairParameterMap_coordinates B b p₀ hp₀ v
      (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hAffine : HasFDerivAt
      (fun v : X ↦ (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀) + v)
      (ContinuousLinearMap.id ℝ X) u :=
    (hasFDerivAt_id u).const_add ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀))
  rw [heq.fderiv_eq, hAffine.fderiv]
  rfl

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairParameter_coordinates_mem_fixed_sample
#print axioms GlobalEmbedding.NormalPolar.actualRepairParameterMap_smooth
#print axioms GlobalEmbedding.NormalPolar.actualRepairParameterMap_coordinate_derivative
