import NormalPolar.MapFamily
import NormalPolar.Response
import Round2.MetricLeftInverse
import Round2.ProbeBridgeSecondForm

/-!
# The native parameter response of the constructed identification on actual maps

This bridges the universal ambient estimate to the total normal-bundle
identification selected by `actualImmersionNormalIdentification`. A genuine
atlas first jet supplies the derivative; the atlas is kept fixed. Equality of
the actual maps' induced metrics supplies the Gram identity. The open parameter
set is preserved and the reserve `q < 1` is fixed before its points.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

theorem norm_fderiv_actualImmersionNormalIdentification_from_firstJet_le
    (F₀ : M → V) (F : P → M → V)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count) (z : M) (hz : z ∈ (A.chart i).source)
    {U : Set P} (hU : IsOpen U) (u d : P) (hu : u ∈ U)
    (q : ℝ) (hq : q < 1)
    (hfirst : DifferentiableAt ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u)
    (hmetric : ∀ v ∈ U, inducedMetric (I := IM) (F v) z = inducedMetric (I := IM) F₀ z)
    (hgap : ∀ v ∈ U, ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) (F v) z).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v)
        (actualImmersionNormalIdentification F₀ (F v) hi₀ (hi v)) z) u d‖ ≤
      polarResponseConstantOn V q hq *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A (F u) i z‖ *
          ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u d‖) := by
  let L₀ := probeAtlasFirstJet A F₀ i z
  let L : P → E →L[ℝ] V := fun v ↦ probeAtlasFirstJet A (F v) i z
  have hn₀ : normalSpace (I := IM) F₀ z = (LinearMap.range L₀.toLinearMap)ᗮ :=
    normalSpace_eq_probeAtlasFirstJet_range A hA F₀ hF₀ i z hz
  have hn (v : P) : normalSpace (I := IM) (F v) z = (LinearMap.range (L v).toLinearMap)ᗮ :=
    normalSpace_eq_probeAtlasFirstJet_range A hA (F v) (hF v) i z hz
  have heq : (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v)
      (actualImmersionNormalIdentification F₀ (F v) hi₀ (hi v)) z) =ᶠ[𝓝 u]
      (fun v ↦ actualPolarOperator (LinearMap.range L₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (L v).toLinearMap)ᗮ.starProjection) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [actualImmersionNormalIdentification_operator F₀ (F v) hi₀ (hi v) z
      ((hgap v hv).trans_lt hq), hn₀, hn v]
  rw [heq.fderiv_eq]
  have hLi : ∀ᶠ v in 𝓝 u, Function.Injective (L v) :=
    Eventually.of_forall (fun v ↦ probeAtlasFirstJet_injective A hA (F v) (hF v) i z hz (hi v z))
  have hLm : ∀ᶠ v in 𝓝 u, (L v).adjoint.comp (L v) = L₀.adjoint.comp L₀ := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact probeAtlasFirstJet_gram_eq_of_inducedMetric_eq A hA F₀ (F v) hF₀ (hF v)
      i z hz (hmetric v hv)
  apply norm_fderiv_actualFramePolarOperator_apply_le_reserve q hq L L₀ u d hfirst hLi hLm
  simpa only [hn₀, hn u] using hgap u hu

end GlobalEmbedding.NormalPolar
