import NormalPolar.ResponseActualMap
import NormalPolar.CompressionPolarResponse

/-!
# Explicit reserve constants for the actual normal identification response

The native normal projection response is derived from the actual fixed-metric
first jet.  The explicit positive-compression response then controls the same
total normal identification on the supplied open parameter domain.  No
normal response bound or identification is an input, and no domain is reduced.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

/-- The explicit coefficient obtained by differentiating the actual positive
compression. It is used with a nonnegative projection reserve q < 1. -/
def normalPolarExplicitResponseConstant (q : ℝ) : ℝ :=
  ((1 - q ^ 2)⁻¹) ^ 2 * q + Real.sqrt ((1 - q ^ 2)⁻¹)

theorem normalPolarExplicitResponseConstant_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ normalPolarExplicitResponseConstant q :=
  add_nonneg (mul_nonneg (sq_nonneg _) hq) (Real.sqrt_nonneg _)

section Frames
variable {P D V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The explicit Q response from a genuine first jet with fixed Gram matrix.
The derivative of its true normal projection is proved by the existing native
fixed-metric projection theorem. -/
theorem norm_fderiv_actualFramePolarOperator_apply_le_explicitReserve
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (q : ℝ) (hq : q < 1)
    (hgap : ‖(LinearMap.range A₀.toLinearMap)ᗮ.starProjection -
      (LinearMap.range (A u).toLinearMap)ᗮ.starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator
        (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      normalPolarExplicitResponseConstant q *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hgap
  apply (norm_fderiv_actualPolarOperator_apply_le_explicit
    (LinearMap.range A₀.toLinearMap)ᗮ
    (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ) u a
    (differentiableAt_actualNormalProjection_fixed_metric A A₀ u hA hinj hmetric)
    q hq hgap).trans
  exact mul_le_mul
    (show ((1 - q ^ 2)⁻¹) ^ 2 * ‖(LinearMap.range A₀.toLinearMap)ᗮ.starProjection -
        (LinearMap.range (A u).toLinearMap)ᗮ.starProjection‖ + Real.sqrt ((1 - q ^ 2)⁻¹) ≤
      normalPolarExplicitResponseConstant q from
        add_le_add (mul_le_mul_of_nonneg_left hgap (sq_nonneg _)) le_rfl)
    (norm_fderiv_actualNormalProjection_fixed_metric_apply_le A A₀ u a hA hinj hmetric)
    (norm_nonneg _) (normalPolarExplicitResponseConstant_nonneg hq0)

end Frames

section ActualMaps
variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The same total actual identification has the explicit positive-compression
response on the original parameter domain.  The local equality needed for
differentiating the total constructor is proved throughout a neighborhood. -/
theorem norm_fderiv_actualImmersionNormalIdentification_from_firstJet_le_explicit
    (F₀ : M → V) (F : P → M → V)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count) (z : M) (hz : z ∈ (A.chart i).source)
    {U : Set P} (hU : IsOpen U) (u a : P) (hu : u ∈ U)
    (q : ℝ) (hq : q < 1)
    (hfirst : DifferentiableAt ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u)
    (hmetric : ∀ v ∈ U, inducedMetric (I := IM) (F v) z = inducedMetric (I := IM) F₀ z)
    (hgap : ∀ v ∈ U, ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) (F v) z).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v)
        (actualImmersionNormalIdentification F₀ (F v) hi₀ (hi v)) z) u a‖ ≤
      normalPolarExplicitResponseConstant q *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
          (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A (F u) i z‖ *
          ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u a‖) := by
  let A₀ := probeAtlasFirstJet A F₀ i z
  let J : P → E →L[ℝ] V := fun v ↦ probeAtlasFirstJet A (F v) i z
  have hn₀ : normalSpace (I := IM) F₀ z = (LinearMap.range A₀.toLinearMap)ᗮ :=
    normalSpace_eq_probeAtlasFirstJet_range A hA F₀ hF₀ i z hz
  have hn (v : P) : normalSpace (I := IM) (F v) z = (LinearMap.range (J v).toLinearMap)ᗮ :=
    normalSpace_eq_probeAtlasFirstJet_range A hA (F v) (hF v) i z hz
  have heq : (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v)
      (actualImmersionNormalIdentification F₀ (F v) hi₀ (hi v)) z) =ᶠ[𝓝 u]
      (fun v ↦ actualPolarOperator (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (J v).toLinearMap)ᗮ.starProjection) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [actualImmersionNormalIdentification_operator F₀ (F v) hi₀ (hi v) z
      ((hgap v hv).trans_lt hq), hn₀, hn v]
  rw [heq.fderiv_eq]
  have hJi : ∀ᶠ v in 𝓝 u, Function.Injective (J v) :=
    Eventually.of_forall (fun v ↦ probeAtlasFirstJet_injective A hA (F v) (hF v) i z hz (hi v z))
  have hJm : ∀ᶠ v in 𝓝 u, (J v).adjoint.comp (J v) = A₀.adjoint.comp A₀ := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact probeAtlasFirstJet_gram_eq_of_inducedMetric_eq A hA F₀ (F v) hF₀ (hF v)
      i z hz (hmetric v hv)
  apply norm_fderiv_actualFramePolarOperator_apply_le_explicitReserve J A₀ u a
    hfirst hJi hJm q hq
  simpa only [hn₀, hn u] using hgap u hu

end ActualMaps
end GlobalEmbedding.NormalPolar
