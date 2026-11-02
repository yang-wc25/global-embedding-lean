import NormalPolar.ParameterDisplacementNorms
import NormalPolar.NativeProbeValueTail
import Round2.ProbeBridgeIncidenceParameterSmooth
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Integrating the actual original parameter C1 estimate

The bound on the original C1 norm of the actual parameter derivative controls
the original spatial C1 displacement between any two parameters in the same
ball. The proof integrates the genuine value and fixed-chart first jet by the
mean value theorem, using the proved native mixed-derivative identity. It
does not assume a zero center or supply a displacement estimate as an input.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- One constant for values and first jets followed by the true reverse
coordinate conversion. It does not depend on the atlas or its cardinality. -/
def probeParameterDisplacementConstant (n N : ℕ) : ℝ :=
  probeAtlasFromNativeConstant n N 1 *
    (nativeValueTailConstant N + probeAtlasDerivativeConstant n N 1)

theorem probeParameterDisplacementConstant_nonneg (n N : ℕ) :
    0 ≤ probeParameterDisplacementConstant n N :=
  mul_nonneg (probeAtlasFromNativeConstant_nonneg n N 1)
    (add_nonneg (nativeValueTailConstant_nonneg N) (probeAtlasDerivativeConstant_nonneg n N 1))

/-- The actual value displacement is obtained by the mean value theorem
on the entire original parameter ball. -/
theorem actual_value_parameter_displacement_of_originalC1
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold) {C : ℝ} (hC : 0 ≤ C)
    (hparameter : ∀ u, ‖u‖ < g.radius → ∀ d,
      probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ g.map t v x) u d) ≤
        ENNReal.ofReal (C * ‖d‖))
    (u v : ProbeParameters r) (hu : ‖u‖ < g.radius) (hv : ‖v‖ < g.radius) (x : M) :
    ‖g.map t u x - g.map t v x‖ ≤ (nativeValueTailConstant N * C) * ‖u - v‖ := by
  have hdiff (w : ProbeParameters r) (hw : w ∈ Metric.ball 0 g.radius) :
      DifferentiableAt ℝ (fun z ↦ g.map t z x) w :=
    actual_parameter_value_differentiableAt_of_joint A hA hcover Metric.isOpen_ball
      (g.map t) (g.joint_smooth t ht htt) w hw x
  have hbound (w : ProbeParameters r) (hw : w ∈ Metric.ball 0 g.radius) :
      ‖fderiv ℝ (fun z ↦ g.map t z x) w‖ ≤ nativeValueTailConstant N * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (nativeValueTailConstant_nonneg N) hC)
    intro d
    have hb := norm_le_of_probeAtlasCj A hA hcover 1
      (fun x ↦ fderiv ℝ (fun z ↦ g.map t z x) w d)
      (mul_nonneg hC (norm_nonneg d)) (hparameter w (by simpa using hw) d) x
    simpa only [nativeValueTailConstant, mul_assoc] using hb
  exact (convex_ball (0 : ProbeParameters r) g.radius).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (by simpa using hv) (by simpa using hu)

/-- The actual first-jet displacement uses the original C1 parameter norm
via the genuine mixed-derivative identity, followed by the same mean value
theorem. No estimate on a substitute first-jet field is assumed. -/
theorem actual_firstJet_parameter_displacement_of_originalC1
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold) {C : ℝ} (hC : 0 ≤ C)
    (hparameter : ∀ u, ‖u‖ < g.radius → ∀ d,
      probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ g.map t v x) u d) ≤
        ENNReal.ofReal (C * ‖d‖))
    (u v : ProbeParameters r) (hu : ‖u‖ < g.radius) (hv : ‖v‖ < g.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖probeAtlasFirstJet A (g.map t u) i x - probeAtlasFirstJet A (g.map t v) i x‖ ≤
      (probeAtlasDerivativeConstant n N 1 * C) * ‖u - v‖ := by
  have hdiff (w : ProbeParameters r) (hw : w ∈ Metric.ball 0 g.radius) :
      DifferentiableAt ℝ (fun z ↦ probeAtlasFirstJet A (g.map t z) i x) w :=
    g.atlas_firstJet_parameter_differentiable A hA i t ht htt w (by simpa using hw) x
      (hA.support_subset i hx)
  have hbound (w : ProbeParameters r) (hw : w ∈ Metric.ball 0 g.radius) :
      ‖fderiv ℝ (fun z ↦ probeAtlasFirstJet A (g.map t z) i x) w‖ ≤
        probeAtlasDerivativeConstant n N 1 * C := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 1) hC)
    intro d
    have hb := g.atlas_firstJet_parameter_derivative_bound_of_originalC1 A hA i t ht htt
      w d (by simpa using hw) x hx (mul_nonneg hC (norm_nonneg d))
      (hparameter w (by simpa using hw) d)
    simpa only [mul_assoc] using hb
  exact (convex_ball (0 : ProbeParameters r) g.radius).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (by simpa using hv) (by simpa using hu)

/-- Original parameter C1 control yields original spatial C1 displacement
for every pair in the unchanged ball. The constant is fixed by n and N. -/
theorem originalC1_parameter_displacement
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold) {C : ℝ} (hC : 0 ≤ C)
    (hparameter : ∀ u, ‖u‖ < g.radius → ∀ d,
      probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ g.map t v x) u d) ≤
        ENNReal.ofReal (C * ‖d‖))
    (u v : ProbeParameters r) (hu : ‖u‖ < g.radius) (hv : ‖v‖ < g.radius) :
    probeAtlasCj A 1 (g.map t u - g.map t v) ≤
      ENNReal.ofReal (probeParameterDisplacementConstant n N * C * ‖u - v‖) := by
  let K := nativeValueTailConstant N + probeAtlasDerivativeConstant n N 1
  have hK : 0 ≤ K := add_nonneg (nativeValueTailConstant_nonneg N)
    (probeAtlasDerivativeConstant_nonneg n N 1)
  have hB : 0 ≤ K * C * ‖u - v‖ := mul_nonneg (mul_nonneg hK hC) (norm_nonneg _)
  have hvalue (i : Fin A.count) (x : M) (_hx : x ∈ A.support i) :
      ‖(g.map t u - g.map t v) x‖ ≤ K * C * ‖u - v‖ := by
    apply (actual_value_parameter_displacement_of_originalC1 g A hA hcover
      t ht htt hC hparameter u v hu hv x).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (probeAtlasDerivativeConstant_nonneg n N 1)) hC)
      (norm_nonneg _)
  have hfirst (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖probeAtlasFirstJet A (g.map t u - g.map t v) i x‖ ≤ K * C * ‖u - v‖ := by
    have hxT := (A.chart i).map_source (hA.support_subset i hx)
    have huD := ((probeAtlas_fixed_coordinate_smooth A hA (g.map t u)
      (g.slice_smooth t u) i).contDiffAt ((A.chart i).open_target.mem_nhds hxT)).differentiableAt
      (by simp)
    have hvD := ((probeAtlas_fixed_coordinate_smooth A hA (g.map t v)
      (g.slice_smooth t v) i).contDiffAt ((A.chart i).open_target.mem_nhds hxT)).differentiableAt
      (by simp)
    have heq : probeAtlasFirstJet A (g.map t u - g.map t v) i x =
        probeAtlasFirstJet A (g.map t u) i x - probeAtlasFirstJet A (g.map t v) i x :=
      fderiv_sub huD hvD
    rw [heq]
    apply (actual_firstJet_parameter_displacement_of_originalC1 g A hA t ht htt
      hC hparameter u v hu hv i x hx).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (nativeValueTailConstant_nonneg N)) hC) (norm_nonneg _)
  have h := probeAtlasC1_le_of_value_firstJet A hA (g.map t u - g.map t v)
    ((g.slice_smooth t u).sub (g.slice_smooth t v)) hB hvalue hfirst
  simpa only [probeParameterDisplacementConstant, K, mul_assoc] using h

end GlobalEmbedding.NormalPolar
