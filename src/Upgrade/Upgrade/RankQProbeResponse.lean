import Upgrade.SupportedIdentifiedCoordinates
import Upgrade.SupportedProbeJointSmooth

/-!
# Actual probe responses in the normalized fixed normal chart

This is a consumer of `ExactProbeFamily` for one fixed global wave list.
The original atlas-framed second-form response is transported through the
fixed base-point symmetric-square inverse and the fixed old normal projection.
Every global remainder is kept, with its explicit fixed norm multiplier.
The value response at the second endpoint is retained even where the leading
cutoff is zero. This file has no incidence-rank assumption or conclusion.

Parameter differentiability of the SAME framed identified true-form field is
derived from the full probe family's actual joint smoothness and normal
identification, through the actual Hessian dictionary. No extra regularity
premise on a second-form field is imposed.
-/

noncomputable section
open Manifold Module Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

section FixedTransport
variable {P S Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- Composition of the already proved fixed-right and normal-projection
bounds. The full differentiated tensor residual remains inside the norm. -/
theorem norm_fixed_normal_right_response_error
    (W : Submodule ℝ Z) [W.HasOrthogonalProjection]
    (C : P → S →L[ℝ] Z) (u : P) (hC : DifferentiableAt ℝ C u)
    (K : S →L[ℝ] S) (d : P) (a : ℝ) (T : S →L[ℝ] Z) :
    ‖fderiv ℝ (fun v ↦ W.orthogonalProjectionOnto.comp ((C v).comp K)) u d -
      a • W.orthogonalProjectionOnto.comp (T.comp K)‖ ≤
        ‖fderiv ℝ C u d - a • T‖ * ‖K‖ := by
  let R : (S →L[ℝ] Z) →L[ℝ] (S →L[ℝ] Z) :=
    (ContinuousLinearMap.compL ℝ S S Z).flip K
  have hR : DifferentiableAt ℝ (fun v ↦ (C v).comp K) u :=
    R.differentiableAt.comp u hC
  exact (fixed_normal_projection_error W (fun v ↦ (C v).comp K) hR d a (T.comp K)).trans
    (fixed_tensor_right_transport_error C hC K d a T)
end FixedTransport

open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Literal second-form response of the one probe family in the actual
normalized source frame and fixed original normal fiber. In particular,
the source frame at z is NOT replaced by its value at the center. -/
theorem ExactProbeFamily.projected_normalized_secondForm_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ A.support i) :
    ‖fderiv ℝ
        (fun v ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
          (probe.normalIdentification t v) x z (probeAtlasNormalizedFrame A hA i x hx z))
        u (Pi.single (l,b) 1) -
      (t ^ ((44 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
        t ^ ((6 : ℝ) / 5))) •
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))‖ ≤
      t ^ ((44 : ℝ) / 5) *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖) := by
  let C : ProbeParameters r → SymmetricSquare E →L[ℝ] V := fun v ↦
    probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (probe.map t v) (probe.slice_smooth t v)
        (probe.normalIdentification t v) z)
  have hC : DifferentiableAt ℝ C u :=
    probe.toProbeGeometry.identified_trueSecondForm_parameter_differentiable
      A hA i t ht htt u hu z (hA.support_subset i hz)
  let K := probeAtlasNormalizationSquare A hA i x hx
  let PN := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
  let T := probeTensorInFrame (probeAtlasFrame A i z) ((waves l).tensor z)
  let a := t ^ ((44 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
    t ^ ((6 : ℝ) / 5))
  have hfun :
      (fun v ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
        (probe.normalIdentification t v) x z (probeAtlasNormalizedFrame A hA i x hx z)) =
      (fun v ↦ PN.comp ((C v).comp K)) := by
    funext v
    exact congrArg (fun R ↦ PN.comp R) (probeTensorInFrame_normalized A hA i x hx z _)
  have hlead : PN.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z)) =
      PN.comp (T.comp K) :=
    congrArg (fun R ↦ PN.comp R) (probeTensorInFrame_normalized A hA i x hx z _)
  rw [hfun, hlead]
  have htransport := norm_fixed_normal_right_response_error
    (normalSpace (I := IM) F₀ x) C u hC K (Pi.single (l,b) 1) a T
  have hraw := probe.secondForm_response t ht htt u hu l b i z hz
  exact htransport.trans ((mul_le_mul_of_nonneg_right hraw (norm_nonneg K)).trans_eq
    (mul_assoc _ _ _))

/-- Same-family value response in the principal-column convention used by
both incidence arguments. The minus sign and returned weight remain literal. -/
theorem ExactProbeFamily.value_response_principal
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (l : Fin r) (b : Bool) (x : M) :
    ‖fderiv ℝ (fun v ↦ probe.map t v x) u (Pi.single (l,b) 1) -
      (t ^ ((56 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase x /
        t ^ ((6 : ℝ) / 5))) • (-((probe.weight l ^ 2)⁻¹) • (waves l).value x)‖ ≤
      t ^ ((56 : ℝ) / 5) * (probe.etaV t + probe.constant * ‖u‖) := by
  have hraw := probe.value_response t ht htt u hu l b x
  have hscale :
      -(t ^ ((56 : ℝ) / 5)) * (probe.weight l ^ 2)⁻¹ *
          probeTrig b (probe.weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5)) =
        (t ^ ((56 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) * -((probe.weight l ^ 2)⁻¹) := by ring
  rw [smul_smul]
  rwa [hscale] at hraw

/-- At the second endpoint only the leading term vanishes. The actual
parameter derivative remains as a controlled GLOBAL remainder. -/
theorem ExactProbeFamily.value_response_away
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (b : Bool) (y : M) (haway : (waves l).cutoff y = 0) :
    ‖fderiv ℝ (fun v ↦ probe.map t v y) u (Pi.single (l,b) 1)‖ ≤
      t ^ ((56 : ℝ) / 5) * (probe.etaV t + probe.constant * ‖u‖) := by
  have hv : (waves l).value y = 0 := by
    simp only [LocalLegalWave.value, haway, zero_smul]
  simpa only [hv, smul_zero, sub_zero] using probe.value_response t ht htt u hu l b y

end GlobalEmbedding.Upgrade
