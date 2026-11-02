import Upgrade.SupportedHessianC3
import Upgrade.SupportedProbeJointSmooth

/-!
# Original probe C³ control of the actual incidence's spatial derivative

The map and Hessian are the actual probe slice in the actual fixed atlas.
The remaining normal-identification derivative bound is displayed literally.
Pointwise orthogonality is used only for the proved operator bound one.
No polar identification is constructed here.
-/

noncomputable section
open Bundle Manifold Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section FixedHessianGeometry
variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup W] [NormedSpace ℝ W]

private noncomputable local instance fixedFirstOperatorNormed :
    NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fixedFirstOperatorSpace :
    NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance fixedBilinearOperatorNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fixedBilinearOperatorSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance fixedSquareOperatorNormed :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fixedSquareOperatorSpace :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

/-- The actual coordinate Hessian is differentiable because the same actual
map is C³ (indeed smooth here). The fixed Hessian lift is the accepted one. -/
theorem coordinateHessianJet_differentiableAt
    (f : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x) :
    DifferentiableAt ℝ (coordinateHessianJet f) x := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hDD : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := hD.fderiv_right (by simp)
  have hH : ContDiffAt ℝ ∞ (coordinateHessianJet f) x :=
    (actualHessianLift (E := E) (F := F)).contDiff.contDiffAt.comp x hDD
  exact hH.differentiableAt (by simp)

/-- Precise actual product-rule bound: DQ times the native Hessian plus Q
times the native third derivative, followed by the fixed source factor. -/
theorem norm_fderiv_projected_identified_hessian_le
    (f : E → F) (Q : E → F →L[ℝ] F) (J : F →L[ℝ] W)
    (K : SymmetricSquare E →L[ℝ] SymmetricSquare E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hQ : DifferentiableAt ℝ Q x)
    (hJ : ‖J‖ ≤ 1) (hQnorm : ‖Q x‖ ≤ 1)
    (L B2 B3 : ℝ) (hDQ : ‖fderiv ℝ Q x‖ ≤ L)
    (h2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B2) (h3 : ‖iteratedFDeriv ℝ 3 f x‖ ≤ B3) :
    ‖fderiv ℝ (fun z ↦ J.comp (((Q z).comp (coordinateHessianJet f z)).comp K)) x‖ ≤
      (L * (actualHessianLiftConstant E F * B2) + actualHessianLiftConstant E F * B3) * ‖K‖ := by
  let H := coordinateHessianJet f
  have hH : DifferentiableAt ℝ H x := coordinateHessianJet_differentiableAt f x hf
  have hHL : 0 ≤ actualHessianLiftConstant E F := actualHessianLiftConstant_nonneg
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ Q x)).trans hDQ
  have hHnorm : ‖H x‖ ≤ actualHessianLiftConstant E F * B2 :=
    (coordinateHessianJet_norm_le_native_second f x).trans (mul_le_mul_of_nonneg_left h2 hHL)
  have hDHnorm : ‖fderiv ℝ H x‖ ≤ actualHessianLiftConstant E F * B3 :=
    (coordinateHessianJet_fderiv_norm_le_native_third f x hf).trans (mul_le_mul_of_nonneg_left h3 hHL)
  have hproduct := norm_fderiv_identified_hessian_product_le Q H x hQ hH
  have hbounded : ‖fderiv ℝ (fun z ↦ (Q z).comp (H z)) x‖ ≤
      L * (actualHessianLiftConstant E F * B2) + actualHessianLiftConstant E F * B3 := by
    apply hproduct.trans
    exact add_le_add (mul_le_mul hDQ hHnorm (norm_nonneg (H x)) hL)
      ((mul_le_mul hQnorm hDHnorm (norm_nonneg (fderiv ℝ H x)) zero_le_one).trans_eq (one_mul _))
  exact (norm_fderiv_fixed_left_right_le J hJ (fun z ↦ (Q z).comp (H z)) x
    (hQ.clm_comp hH) K).trans (mul_le_mul_of_nonneg_right hbounded (norm_nonneg K))

end FixedHessianGeometry

section ActualSpatialRestriction
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem actual_spatial_differentiableAt
    (f : P × X → Y) {z : P × X} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun v ↦ f (z.1, v)) z.2 :=
  (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).differentiableAt

end ActualSpatialRestriction

section ActualProbe
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance fixedNormalOperatorNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fixedNormalOperatorSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual normal-identification operator is spatially differentiable
in the same fixed atlas. This follows from its original joint smoothness. -/
theorem ProbeGeometry.normalIdentification_atlas_spatial_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ (fun v : E ↦ normalIdentificationOperator (n := n)
      F₀ (g.map t u) (g.normalIdentification t u) ((A.chart i).symm v)) (A.chart i z) := by
  have hQ := contDiffOn_actual_parameter_atlas_pullback A hA i
    (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n)
      F₀ (g.map t w.1) (g.normalIdentification t w.1) w.2)
    (g.normalIdentification_smooth t ht htt)
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, (A.chart i).map_source hz⟩
  have hD : DifferentiableAt ℝ (fun w : ProbeParameters r × E ↦ normalIdentificationOperator (n := n)
      F₀ (g.map t w.1) (g.normalIdentification t w.1) ((A.chart i).symm w.2)) (u, A.chart i z) :=
    (hQ.contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  exact actual_spatial_differentiableAt _ hD

/-- Original spatial C³ control supplies the actual incidence derivative
bound. The ONLY added quantitative input is the literal spatial derivative
of the selected normal-identification operator in this same fixed atlas.
This is precisely the quantity supplied by a controlled identification;
orthogonality is never used to infer it. -/
theorem ExactProbeFamily.actual_supported_coordinate_spatial_derivative_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i) (L : ℝ)
    (hDQ : ‖fderiv ℝ (fun v : E ↦ normalIdentificationOperator (n := n) F₀
      (probe.map t u) (probe.normalIdentification t u) ((A.chart i).symm v)) (A.chart i z)‖ ≤ L) :
    ‖fderiv ℝ (fun v : E ↦ actualSupportedProbeCoordinate F₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hx (u, v)) (A.chart i z)‖ ≤
      (L * (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * probe.constant)) +
        actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 3 * probe.constant)) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖ := by
  let f := probe.map t u ∘ (A.chart i).symm
  let Q := fun v : E ↦ normalIdentificationOperator (n := n) F₀
    (probe.map t u) (probe.normalIdentification t u) ((A.chart i).symm v)
  let J := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
  let K := probeAtlasNormalizationSquare A hA i x hx
  have hzS := hA.support_subset i hz
  have hzT := (A.chart i).map_source hzS
  have hf : ContDiffAt ℝ ∞ f (A.chart i z) :=
    (probeAtlas_fixed_coordinate_smooth A hA (probe.map t u) (probe.slice_smooth t u) i).contDiffAt
      ((A.chart i).open_target.mem_nhds hzT)
  have hQ : DifferentiableAt ℝ Q (A.chart i z) :=
    probe.toProbeGeometry.normalIdentification_atlas_spatial_differentiable A hA i t ht htt u hu z hzS
  have hQnorm : ‖Q (A.chart i z)‖ ≤ 1 := by
    dsimp only [Q]
    rw [(A.chart i).left_inv hzS]
    exact normalIdentificationOperator_norm_le_one F₀ (probe.map t u) (probe.normalIdentification t u) z
  have h2 := probeAtlas_native_derivative_bound A hA (probe.map t u) (probe.slice_smooth t u)
    probe.constant_nonneg (probe.spatial_C3 t ht htt u hu) (show 2 ≤ 3 by norm_num) i z hz
  have h3 := probeAtlas_native_derivative_bound A hA (probe.map t u) (probe.slice_smooth t u)
    probe.constant_nonneg (probe.spatial_C3 t ht htt u hu) (show 3 ≤ 3 by norm_num) i z hz
  have heq : (fun v : E ↦ actualSupportedProbeCoordinate F₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hx (u, v)) =ᶠ[𝓝 (A.chart i z)]
      (fun v : E ↦ J.comp (((Q v).comp (coordinateHessianJet f v)).comp K)) := by
    filter_upwards [(A.chart i).open_target.mem_nhds hzT] with v hv
    exact actualSupportedProbeCoordinate_eq_identified_hessian F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u, v) hv
  rw [heq.fderiv_eq]
  exact norm_fderiv_projected_identified_hessian_le f Q J K (A.chart i z) hf hQ
    (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto_norm_le hQnorm
    L (probeAtlasDerivativeConstant n N 2 * probe.constant)
      (probeAtlasDerivativeConstant n N 3 * probe.constant) hDQ h2 h3

end ActualProbe

#print axioms coordinateHessianJet_differentiableAt
#print axioms norm_fderiv_projected_identified_hessian_le
#print axioms ProbeGeometry.normalIdentification_atlas_spatial_differentiable
#print axioms ExactProbeFamily.actual_supported_coordinate_spatial_derivative_bound

end GlobalEmbedding.Upgrade
