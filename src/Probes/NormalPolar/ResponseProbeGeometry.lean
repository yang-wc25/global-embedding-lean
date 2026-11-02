import NormalPolar.ResponseActualMap
import Round2.ProbeBridgeIncidenceParameterSmooth
import Round2.ProbeBridgeIncidenceParameter

/-!
# Full identified second-form response for the constructed same-Q geometry

The geometry below is built from the supplied actual maps by the explicit
normal-polar constructor. No pre-existing normal identification or second-form
response is transported or reused. The original native Hessian response is
converted by the existing exact bridge, and its two additional terms remain:
the same-Q zeroth-order gap on the principal tensor, and the actual Q derivative
on the current Hessian. The latter is now bounded from the actual first jet.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

section ActualGeometry
variable
    (F₀ : M → (EuclideanSpace ℝ (Fin N))) (hF₀ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) F₀ x))
    {r : ℕ} (F : ℝ → ProbeParameters r → M → (EuclideanSpace ℝ (Fin N)))
    (radius threshold : ℝ) (hradius : 0 < radius) (hthreshold : 0 < threshold)
    (hF : ∀ t u, ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ (F t u))
    (hi : ∀ t u x, Function.Injective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) (F t u) x))
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) (F t u) x = inducedMetric (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) F₀ x)
    (q : ℝ) (hq : q < 1)
    (hgap : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      ‖(normalSpace (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) F₀ x).starProjection -
        (normalSpace (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) (F t u) x).starProjection‖ ≤ q)

/-- Parameter differentiability of the genuine first jet is derived from
the same map's joint smoothness by the existing probe geometry bridge. -/
theorem actualProbeGeometry_normal_response_from_firstJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).map t v)
        ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).normalIdentification t v) z) u d‖ ≤
      polarResponseConstantOn V q hq *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A (F t u) i z‖ *
          ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F t v) i z) u d‖) := by
  apply norm_fderiv_actualImmersionNormalIdentification_from_firstJet_le F₀ (F t)
    hF₀ (hF t) hi₀ (hi t) A hA i z hz (U := Metric.ball 0 radius) Metric.isOpen_ball u d
    (by simpa using hu) q hq
    ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).atlas_firstJet_parameter_differentiable A hA i t ht htt u hu z hz)
  · intro v hv
    exact hmetric t ht htt v (by simpa using hv) z
  · intro v hv
    exact hgap t ht htt v (by simpa using hv) z

/-- The actual original parameter C¹ budget gives a quantitative same-Q
response on the unchanged original atlas supports and parameter ball. -/
theorem actualProbeGeometry_normal_response_from_originalC1
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < radius)
    (z : M) (hz : z ∈ A.support i) {b : ℝ} (hb : 0 ≤ b)
    (hbudget : probeAtlasCj A 1 (fun y ↦ fderiv ℝ (fun v ↦ F t v y) u d) ≤
      ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).map t v)
        ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).normalIdentification t v) z) u d‖ ≤
      polarResponseConstantOn V q hq *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A F₀ i z‖ *
          (probeAtlasDerivativeConstant n N 1 * b)) := by
  have hD := actualProbeGeometry_normal_response_from_firstJet F₀ hF₀ hi₀ F radius threshold
    hradius hthreshold hF hi hjoint hmetric q hq hgap A hA i t ht htt u d hu z
    (hA.support_subset i hz)
  rw [probeAtlasFirstJet_norm_eq_of_inducedMetric_eq A hA F₀ (F t u) hF₀ (hF t u)
    i z (hA.support_subset i hz) (hmetric t ht htt u hu z)] at hD
  apply hD.trans
  apply mul_le_mul_of_nonneg_left _ (polarResponseConstantOn_nonneg q hq)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).atlas_firstJet_parameter_derivative_bound_of_originalC1 A hA i t ht htt
    u d hu z hz hb hbudget

/-- This is the full native identified-form response, for the canonical Q
built from the actual map. It keeps both geometric error terms and bounds
the derivative term by the supplied actual first-jet response. -/
theorem actualProbeGeometry_secondForm_response_native_bound
    (wave : LocalLegalWave F₀ hF₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < radius)
    (z : M) (hz : z ∈ (A.chart i).source) (coefficient : ℝ) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).map t v) ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).slice_smooth t v)
          ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ ≤
      actualHessianLiftConstant E V *
        ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (F t v ∘ (A.chart i).symm)) (A.chart i z)) u d -
          coefficient • phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
            (wave.value ∘ (A.chart i).symm) (A.chart i z)‖ +
      ‖actualPolarOperator (normalSpace (I := IM) F₀ z).starProjection
          (normalSpace (I := IM) (F t u) z).starProjection -
          (normalSpace (I := IM) F₀ z).starProjection‖ *
        ‖coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ +
      (polarResponseConstantOn V q hq *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A (F t u) i z‖ *
          ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F t v) i z) u d‖)) *
        ‖probeAtlasSecondJet A (F t u) i z‖ := by
  have h := (probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).identified_secondForm_response_native_bound wave A hA i t ht htt
    u d hu z hz coefficient
  have hQ := actualProbeGeometry_normal_response_from_firstJet F₀ hF₀ hi₀ F radius threshold
    hradius hthreshold hF hi hjoint hmetric q hq hgap A hA i t ht htt u d hu z hz
  have heq : normalIdentificationOperator (n := n) F₀ ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).map t u)
      ((probeGeometryOfActualImmersions F₀ hF₀ hi₀ F
  radius threshold hradius hthreshold hF hi hjoint hmetric
  (fun t ht htt u hu x ↦ lt_of_le_of_lt (hgap t ht htt u hu x) hq)).normalIdentification t u) z =
      actualPolarOperator (normalSpace (I := IM) F₀ z).starProjection
        (normalSpace (I := IM) (F t u) z).starProjection :=
    actualImmersionNormalIdentification_operator F₀ (F t u) hi₀ (hi t u) z
      ((hgap t ht htt u hu z).trans_lt hq)
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)))

end ActualGeometry
end GlobalEmbedding.NormalPolar
