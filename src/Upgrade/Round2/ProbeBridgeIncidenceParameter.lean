import Round2.ProbeBridgeIncidenceParameterSmooth
import Round2.GaugeIncidenceZeros

/-!
# Actual incidence parameter derivatives with no quantitative parameter DQ

At a zero of the SAME actual defining equation, the normal-coordinate orbit
part is killed by its native derivative. The moving-tangent correction stays
explicit and is the parameter derivative of the actual first jet, whose
original C¹ bound is proved in the preceding file. This does not assert a
response bound for the entire identified second form away from the zero set.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

-- Cache Mathlib's unchanged native bilinear operator instances. This avoids
-- repeated expensive search without changing any checker resource limit.
private noncomputable local instance parameterBridgeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance parameterBridgeBilinearNorm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance parameterBridgeBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance parameterBridgeFormNorm (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance parameterBridgeFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- Joint smoothness supplies parameter differentiability of the actual
first jet, not a separately chosen first-derivative carrier. -/
theorem ProbeGeometry.atlas_firstJet_parameter_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ (fun v ↦ probeAtlasFirstJet A (g.map t v) i z) u := by
  have hf := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)
  have hopen : IsOpen (Metric.ball (0 : ProbeParameters r) g.radius ×ˢ (A.chart i).target) :=
    Metric.isOpen_ball.prod (A.chart i).open_target
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, (A.chart i).map_source hz⟩
  exact actual_parameter_differentiableAt _
    (((contDiffOn_actual_spatial_fderiv hopen hf).contDiffAt
      (hopen.mem_nhds hw)).differentiableAt (by simp))

/-- The actual coordinate Hessian parameter derivative is the fixed
continuous-linear Hessian lift of its native bilinear derivative. -/
theorem ProbeGeometry.atlas_secondJet_parameter_derivative_eq
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    fderiv ℝ (fun v ↦ probeAtlasSecondJet A (g.map t v) i z) u d =
      actualHessianLift (fderiv ℝ
        (fun v ↦ fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)) u d) := by
  have hH := (g.atlas_hessian_parameter_factors_differentiable A hA i
    t ht htt u hu z hz).2
  exact congrArg
    (fun D : ProbeParameters r →L[ℝ] (SymmetricSquare E →L[ℝ] V) ↦ D d)
    ((actualHessianLift («E» := E) (F := V)).hasFDerivAt.comp u hH.hasFDerivAt).fderiv

/-- Exact parameter gauge cancellation for the actual normalized incidence
coordinate. The pointwise normal right inverse is constructed from the SAME
Q. Its derivative and its norm are never requested. The orbit premise is
discharged below for the native Schur and supported equations at their zeros. -/
theorem ProbeGeometry.actual_incidence_parameter_gauge_cancellation
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) →L[ℝ] Y) :
    let C := fun v ↦ actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
      (g.normalIdentification t) A hA i x hx (v, A.chart i z)
    (∀ L : normalSpace (I := IM) F₀ x →L[ℝ] normalSpace (I := IM) F₀ x,
      D (L.comp (C u)) = 0) →
    D (fderiv ℝ C u d) = D
      ((gaugeActualNormalOperator F₀ (g.map t u) (g.normalIdentification t u) x z).comp
        ((fderiv ℝ (fun v ↦ probeAtlasSecondJet A (g.map t v) i z) u d -
          (fderiv ℝ (fun v ↦ probeAtlasFirstJet A (g.map t v) i z) u d).comp
            ((probeAtlasTangentLeftInverse A (g.map t u) i z).comp
              (probeAtlasSecondJet A (g.map t u) i z))).comp
                (probeAtlasNormalizationSquare A hA i x hx))) := by
  intro C hD
  let T := fun v : ProbeParameters r ↦
    gaugeActualNormalOperator F₀ (g.map t v) (g.normalIdentification t v) x z
  let L := fun v : ProbeParameters r ↦ probeAtlasFirstJet A (g.map t v) i z
  let H := fun v : ProbeParameters r ↦ probeAtlasSecondJet A (g.map t v) i z
  let Ks := probeAtlasNormalizationSquare A hA i x hx
  let Hs := fun v : ProbeParameters r ↦ (H v).comp Ks
  let K := probeAtlasTangentLeftInverse A (g.map t u) i z
  let R := gaugeActualNormalRightInverse F₀ (g.map t u) himm₀
    (g.normalIdentification t u) x z hgap
  obtain ⟨hQ, hRaw⟩ := g.atlas_hessian_parameter_factors_differentiable
    A hA i t ht htt u hu z hz
  have hT : DifferentiableAt ℝ T u :=
    (differentiableAt_const (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto).clm_comp hQ
  have hL : DifferentiableAt ℝ L u :=
    g.atlas_firstJet_parameter_differentiable A hA i t ht htt u hu z hz
  have hH : DifferentiableAt ℝ H u :=
    (actualHessianLift («E» := E) (F := V)).differentiableAt.comp u hRaw
  have hHs : DifferentiableAt ℝ Hs u := hH.clm_comp (differentiableAt_const Ks)
  have hTL : ∀ᶠ v in 𝓝 u, (T v).comp (L v) = 0 :=
    Filter.Eventually.of_forall fun v ↦ gaugeActualNormalOperator_comp_firstJet_zero
      A hA F₀ (g.map t v) (g.slice_smooth t v) (g.normalIdentification t v) i x z hz
  have himm : ∀ q, Function.Injective (mfderiv IM 𝓘(ℝ, V) (g.map t u) q) :=
    fun q ↦ immersion_of_inducedMetric_eq F₀ (g.map t u) q
      (g.metric t ht htt u hu q) (himm₀ q)
  have hsplit : R.comp (T u) + (L u).comp K = ContinuousLinearMap.id ℝ V :=
    gaugeActualNormal_tangent_split A hA F₀ (g.map t u) (g.slice_smooth t u)
      himm₀ himm (g.normalIdentification t u) i x z hz hgap
  have hsame : C = fun v ↦ (T v).comp (Hs v) := by
    funext v
    dsimp only [C]
    rw [actualSupportedProbeCoordinate_eq_identified_hessian F₀ (g.map t)
      (g.slice_smooth t) (g.normalIdentification t) A hA i x hx (v, A.chart i z)
      ((A.chart i).map_source hz)]
    simp only [(A.chart i).left_inv hz]
    apply ContinuousLinearMap.ext
    intro q
    rfl
  have hD' : ∀ L' : normalSpace (I := IM) F₀ x →L[ℝ] normalSpace (I := IM) F₀ x,
      D (L'.comp ((T u).comp (Hs u))) = 0 := by
    intro L'
    rw [← congrFun hsame u]
    exact hD L'
  rw [hsame]
  have h := fderiv_incidence_gauge_cancellation T L Hs u hT hL hHs hTL R K hsplit D hD' d
  rw [fderiv_fixed_tensor_right_transport H hH Ks d] at h
  exact h.trans (congrArg D (by
    apply ContinuousLinearMap.ext
    intro q
    simp only [T, L, H, Hs, K, Ks, ContinuousLinearMap.comp_apply, sub_apply, map_sub]))

#print axioms ProbeGeometry.atlas_firstJet_parameter_differentiable
#print axioms ProbeGeometry.atlas_secondJet_parameter_derivative_eq
#print axioms ProbeGeometry.actual_incidence_parameter_gauge_cancellation

end GlobalEmbedding.Upgrade
