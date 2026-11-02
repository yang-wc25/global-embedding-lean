import Upgrade.SupportedProbeResponse
import Upgrade.SupportedActualAvoidance
import GlobalEmbedding.Paper.AvoidanceCountableLocalNull

/-!
# Supported-kernel avoidance for the actual full probe family

The parameter space is the original sine/cosine array, not a new probe
family. A fixed finite-dimensional linear coordinate equivalence permits
direct use of the accepted Euclidean local avoidance theorem. All incidence
equations below are composed with the actual new true second form. Native
probe responses, current leading-field variation, and actual tensor
closeness imply the rank; no required incidence rank is assumed.
-/

noncomputable section
open Bundle Manifold Set Module MeasureTheory
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- Fixed coordinates on the original finite sine/cosine parameter array. -/
def probeParameterCoordinates (r : ℕ) :
    ProbeParameters r ≃L[ℝ] (Fin (finrank ℝ (ProbeParameters r)) → ℝ) :=
  (Module.finBasis ℝ (ProbeParameters r)).equivFun.toContinuousLinearEquiv

theorem finrank_probeParameters (r : ℕ) :
    finrank ℝ (ProbeParameters r) = 2 * r := by
  simp [ProbeParameters, Nat.mul_comm]

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original parameter projection in the fixed coordinates used by
the accepted null-image theorem. -/
def supportedProbeParameterProjection (r : ℕ) :
    ProbeParameters r × E →L[ℝ] (Fin (finrank ℝ (ProbeParameters r)) → ℝ) :=
  (probeParameterCoordinates r).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ (ProbeParameters r) E)

private theorem supported_probe_local_null_of_derived_rank
    {r k : ℕ} {Ω : Set (ProbeParameters r × E)} (hn : 4 ≤ n)
    (hΩ : IsOpen Ω) {f : ProbeParameters r × E → Fin k → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) {w : ProbeParameters r × E} (hw : w ∈ Ω)
    (hzero : f w = 0)
    (hrank : n * (n - 1) / 2 ≤ finrank ℝ (LinearMap.range (fderiv ℝ f w).toLinearMap)) :
    ∃ U : Set (ProbeParameters r × E), IsOpen U ∧ w ∈ U ∧ U ⊆ Ω ∧
      volume (supportedProbeParameterProjection (n := n) r '' (U ∩ f ⁻¹' {0})) = 0 := by
  have hnq := supported_source_dimension_strict hn
  have hdim : finrank ℝ (ProbeParameters r × E) = finrank ℝ (ProbeParameters r) + n := by simp
  have hrequired : finrank ℝ (ProbeParameters r × E) <
      finrank ℝ (ProbeParameters r) + finrank ℝ (LinearMap.range (fderiv ℝ f w).toLinearMap) := by
    rw [hdim]
    omega
  exact avoidance_euclidean_local_projection_null hΩ hf
    (supportedProbeParameterProjection (n := n) r).contDiff.contDiffOn hw hzero hrequired

/-- One geometric tolerance is chosen BEFORE the eventual global wave count,
list, returned frequencies, parameter, and scale. The complete native probe
response and the unweighted actual tensor variation imply the incidence rank.
The desired rank is not a premise. This rank statement alone makes no claim
of supported-kernel avoidance when n=3. -/
theorem SupportedLocalWavePacket.exact_probe_incidence_of_tolerance
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedLocalWavePacket F₀ hF₀ x y)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) (δ : ℝ) (hδ : 0 < δ)
    (hstable : ∀ (C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
      (T' : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x),
      ‖C - LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)‖ < δ →
      (∀ j, ‖T' j - (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)‖ < δ) →
      C ∈ p.chart.domain ∧ LinearIndependent ℝ (fun j ↦ fderiv ℝ p.chart.equation C (T' j))) :
    let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
      (labels : Fin (n * (n - 1) / 2) → Fin r),
      (∀ j, waves (labels j) = p.waves j) →
      ∀ (probe : ExactProbeFamily F₀ hF₀ A waves)
        (t : ℝ), 0 < t → t < probe.threshold →
      ∀ (u : ProbeParameters r), ‖u‖ < probe.radius →
      ∀ (z : M), z ∈ A.support i →
      let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx
      ‖C (u, A.chart i z) - B‖ < δ →
      (probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ ≤ δ / 16 →
      (∀ j, ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves (labels j)).tensor z)) -
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((waves (labels j)).tensor x)‖ ≤ δ / 16) →
      C (u, A.chart i z) ∈ p.chart.domain ∧
        n * (n - 1) / 2 ≤ finrank ℝ
          (LinearMap.range (fderiv ℝ (p.chart.equation ∘ C) (u, A.chart i z)).toLinearMap) := by
  dsimp only
  let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
  let T : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    fun j ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)
  intro r waves labels hlabels probe t ht htt u hu z hz hclose hbudget hvariation
  let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
    (probe.normalIdentification t) A hA i x hx
  let σ := t ^ ((44 : ℝ) / 5)
  let θ := fun j ↦ probe.weight (labels j) * (waves (labels j)).phase z / t ^ ((6 : ℝ) / 5)
  let d := fun (b : Bool) (j : Fin (n * (n - 1) / 2)) ↦
    ((Pi.single (labels j, b) 1 : ProbeParameters r), (0 : E))
  let R := fun (b : Bool) (j : Fin (n * (n - 1) / 2)) ↦
    fderiv ℝ C (u, A.chart i z) (d b j) - (σ * probeTrig b (θ j)) • T j
  have hσ : 0 < σ := Real.rpow_pos_of_pos ht _
  have hw : (u, A.chart i z) ∈ Metric.ball 0 probe.radius ×ˢ (A.chart i).target :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu,
      (A.chart i).map_source (hA.support_subset i hz)⟩
  have hC : DifferentiableAt ℝ C (u, A.chart i z) :=
    ((probe.toProbeGeometry.actual_supported_coordinate_smooth A hA i x hx t ht htt).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have herr (b : Bool) (j : Fin (n * (n - 1) / 2)) : ‖R b j‖ ≤ σ * δ / 8 := by
    have hraw := probe.actual_supported_coordinate_response_reference hA t ht htt u hu
      (labels j) b i x hx z hz
      ((normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((waves (labels j)).tensor x))
      (δ / 16) (hvariation j)
    rw [hlabels j] at hraw
    have hraw' : ‖R b j‖ ≤ σ *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ + δ / 16) := by
      simpa only [R, C, d, σ, θ, T, hlabels j] using hraw
    have hsmall := mul_le_mul_of_nonneg_left (add_le_add_right hbudget (δ / 16)) hσ.le
    calc
      ‖R b j‖ ≤ σ *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ + δ / 16) := hraw'
      _ ≤ σ * (δ / 16 + δ / 16) := by simpa only [add_comm] using hsmall
      _ = σ * δ / 8 := by ring
  apply supported_paired_incidence_of_finite_tolerance p.chart T δ hδ hstable
    C (u, A.chart i z) σ (d false) (d true) θ
    (R false) (R true) hC hσ hclose
  · intro j
    dsimp only [R, probeTrig]
    simp only [Bool.false_eq_true, ite_false]
    abel
  · intro j
    dsimp only [R, probeTrig]
    simp only [ite_true]
    abel
  · exact herr false
  · exact herr true

/-- Choose the actual tolerance before the eventual global wave count; the
preceding theorem is the entrance for an already prepared identical margin. -/
theorem SupportedLocalWavePacket.exists_exact_probe_incidence_tolerance
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedLocalWavePacket F₀ hF₀ x y)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) :
    let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
      (labels : Fin (n * (n - 1) / 2) → Fin r),
      (∀ j, waves (labels j) = p.waves j) →
      ∀ (probe : ExactProbeFamily F₀ hF₀ A waves)
        (t : ℝ), 0 < t → t < probe.threshold →
      ∀ (u : ProbeParameters r), ‖u‖ < probe.radius →
      ∀ (z : M), z ∈ A.support i →
      let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx
      ‖C (u, A.chart i z) - B‖ < δ →
      (probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ ≤ δ / 16 →
      (∀ j, ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves (labels j)).tensor z)) -
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((waves (labels j)).tensor x)‖ ≤ δ / 16) →
      C (u, A.chart i z) ∈ p.chart.domain ∧
        n * (n - 1) / 2 ≤ finrank ℝ
          (LinearMap.range (fderiv ℝ (p.chart.equation ∘ C) (u, A.chart i z)).toLinearMap) := by
  dsimp only
  let T : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    fun j ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)
  obtain ⟨δ, hδ, hstable⟩ := supported_equation_finite_column_tolerance p.chart T p.normal_columns
  exact ⟨δ, hδ, p.exact_probe_incidence_of_tolerance A hA i hx δ hδ hstable⟩

/-- Local removal of the ORIGINAL supported-kernel incidence for the actual
full probe family. The same previously prepared δ is consumed. Joint
smoothness and rank are derived from the full probe geometry and responses;
only the literal closeness, unweighted leading variation, and quantitative
remainder budget are checked at the actual incidence. -/
theorem SupportedLocalWavePacket.exact_probe_supported_local_null
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedLocalWavePacket F₀ hF₀ x y) (hn : 4 ≤ n)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) (δ : ℝ) (hδ : 0 < δ)
    (hstable : ∀ (C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
      (T' : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x),
      ‖C - LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)‖ < δ →
      (∀ j, ‖T' j - (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)‖ < δ) →
      C ∈ p.chart.domain ∧ LinearIndependent ℝ (fun j ↦ fderiv ℝ p.chart.equation C (T' j)))
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : Fin (n * (n - 1) / 2) → Fin r) (hlabels : ∀ j, waves (labels j) = p.waves j)
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (Ω : Set (ProbeParameters r × E)) (hΩ : IsOpen Ω)
    (hadmissible : ∀ w ∈ Ω, ‖w.1‖ < probe.radius ∧ w.2 ∈ (A.chart i).target ∧
      ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2)).starProjection -
        (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i) (hw : (u, A.chart i z) ∈ Ω)
    (hsupported : HasSupportedKernel (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z))
    (hclose : ‖actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, A.chart i z) -
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)‖ < δ)
    (hbudget : (probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ ≤ δ / 16)
    (hvariation : ∀ j, ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves (labels j)).tensor z)) -
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((waves (labels j)).tensor x)‖ ≤ δ / 16) :
    ∃ U : Set (ProbeParameters r × E), IsOpen U ∧ (u, A.chart i z) ∈ U ∧ U ⊆ Ω ∧
      volume (supportedProbeParameterProjection (n := n) r '' {w | w ∈ U ∧
        HasSupportedKernel (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1)
          ((A.chart i).symm w.2))}) = 0 := by
  let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
    (probe.normalIdentification t) A hA i x hx
  let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
  obtain ⟨hdom, hrank⟩ := p.exact_probe_incidence_of_tolerance A hA i hx δ hδ hstable
    r waves labels hlabels probe t ht htt u hu z hz hclose hbudget hvariation
  have hC : ContDiffOn ℝ ∞ C Ω :=
    (probe.toProbeGeometry.actual_supported_coordinate_smooth A hA i x hx t ht htt).mono
      (fun w hw ↦ ⟨by simpa only [Metric.mem_ball, dist_zero_right] using (hadmissible w hw).1,
        (hadmissible w hw).2.1⟩)
  let Ω' := Ω ∩ C ⁻¹' p.chart.domain
  have hΩ' : IsOpen Ω' := hC.continuousOn.isOpen_inter_preimage hΩ p.chart.isOpen_domain
  have hw' : (u, A.chart i z) ∈ Ω' := ⟨hw, hdom⟩
  let f := p.chart.equation ∘ C
  have hf : ContDiffOn ℝ ∞ f Ω' :=
    p.chart.contDiffOn_equation.comp (hC.mono inter_subset_left) (fun _ hw ↦ hw.2)
  have hzero (w : ProbeParameters r × E) (hw : w ∈ Ω') :
      f w = 0 ↔ HasSupportedKernel
        (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1) ((A.chart i).symm w.2)) :=
    actualSupportedProbeCoordinate_equation_zero_iff F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx w (hadmissible w hw.1).2.1
      (hadmissible w hw.1).2.2 B p.chart hw.2
  have hwzero : f (u, A.chart i z) = 0 := (hzero _ hw').mpr (by
    exact ((A.chart i).left_inv (hA.support_subset i hz)).symm ▸ hsupported)
  obtain ⟨U, hU, hwU, hUsub, hnull⟩ := supported_probe_local_null_of_derived_rank
    hn hΩ' hf hw' hwzero hrank
  refine ⟨U, hU, hwU, fun w hw ↦ (hUsub hw).1, ?_⟩
  apply measure_mono_null (image_mono ?_) hnull
  intro w hw
  exact ⟨hw.1, (hzero w (hUsub hw.1)).mpr hw.2⟩

#print axioms probeParameterCoordinates
#print axioms finrank_probeParameters
#print axioms supportedProbeParameterProjection
#print axioms SupportedLocalWavePacket.exact_probe_incidence_of_tolerance
#print axioms SupportedLocalWavePacket.exists_exact_probe_incidence_tolerance
#print axioms SupportedLocalWavePacket.exact_probe_supported_local_null

end GlobalEmbedding.Upgrade
