import Upgrade.SupportedProbeAvoidance
import Upgrade.CompactSupportedPreparation
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual supported avoidance on the preselected geometric neighborhood

The neighborhood and tolerance are the ones constructed before finite-cover
flattening and before the original probes provider returns its weights. This
consumer retains that same neighborhood, derives its actual joint incidence
rank from the full probe estimates, and applies the accepted local-to-global
null-image theorem. No required rank or new bad-set predicate is supplied.
-/

noncomputable section
open Bundle Manifold Set Module MeasureTheory
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- A null exceptional set in fixed coordinates leaves a parameter in every
positive ball of the ORIGINAL probe parameter array, including dimension zero. -/
theorem exists_small_probe_parameter_outside_null
    {r : ℕ} (Bad : Set (ProbeParameters r)) (ρ : ℝ) (hρ : 0 < ρ)
    (hnull : volume (probeParameterCoordinates r '' Bad) = 0) :
    ∃ u : ProbeParameters r, ‖u‖ < ρ ∧ u ∉ Bad := by
  by_contra h
  have hsub : Metric.ball (0 : ProbeParameters r) ρ ⊆ Bad := by
    intro u hu
    by_contra hnot
    apply h
    exact ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu, hnot⟩
  have hzero := measure_mono_null (image_mono hsub) hnull
  have hopen : IsOpen (probeParameterCoordinates r '' Metric.ball (0 : ProbeParameters r) ρ) :=
    (probeParameterCoordinates r).toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hnonempty : (probeParameterCoordinates r '' Metric.ball (0 : ProbeParameters r) ρ).Nonempty :=
    ⟨probeParameterCoordinates r 0, 0, Metric.mem_ball_self hρ, rfl⟩
  exact hopen.measure_ne_zero volume hnonempty hzero

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual previously prepared source neighborhood, in the actual
inverse chart and paired with the ORIGINAL parameter ball. -/
def SupportedPreparedNeighborhood.probeDomain
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : SupportedLocalWavePacket F₀ hF₀ x y} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : SupportedPreparedNeighborhood A hA packet i hx) (r : ℕ) (ρ : ℝ) :
    Set (ProbeParameters r × E) :=
  Metric.ball 0 ρ ×ˢ ((A.chart i).target ∩ (A.chart i).symm ⁻¹' p.neighborhood)

theorem SupportedPreparedNeighborhood.probeDomain_open
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : SupportedLocalWavePacket F₀ hF₀ x y} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : SupportedPreparedNeighborhood A hA packet i hx) (r : ℕ) (ρ : ℝ) :
    IsOpen (p.probeDomain r ρ) :=
  Metric.isOpen_ball.prod ((A.chart i).continuousOn_symm.isOpen_inter_preimage
    (A.chart i).open_target p.neighborhood_open)

/-- Actual supported bad parameters on the same preselected neighborhood
form a null set. The current true-form displacement from the actual reference
field and the quantitative probe budget are explicit. All other geometric
inputs, leading-field variation, smoothness, and rank are supplied by the
prepared packet and the full probe family. -/
theorem SupportedPreparedNeighborhood.exact_probe_supported_bad_parameters_null
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : SupportedLocalWavePacket F₀ hF₀ x y} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : SupportedPreparedNeighborhood A hA packet i hx) (hn : 4 ≤ n)
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : Fin (n * (n - 1) / 2) → Fin r) (hlabels : ∀ j, waves (labels j) = packet.waves j)
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (ρ : ℝ) (hρ : 0 < ρ) (hρradius : ρ ≤ probe.radius)
    (hbudget : (probe.etaB t + probe.constant * ρ) *
      ‖probeAtlasNormalizationSquare A hA i x (hA.support_subset i (interior_subset hx))‖ ≤ p.tolerance / 16)
    (hnew : ∀ (u : ProbeParameters r), ‖u‖ < ρ → ∀ z ∈ p.neighborhood,
      ‖actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x (hA.support_subset i (interior_subset hx))
          (u, A.chart i z) -
        normalizedReferenceForm A hA F₀ i x (hA.support_subset i (interior_subset hx)) z‖ ≤
          p.tolerance / 2) :
    volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < ρ ∧
      ∃ z ∈ p.neighborhood, HasSupportedKernel
        (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z)}) = 0 := by
  let hxS := hA.support_subset i (interior_subset hx)
  let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
    (probe.normalIdentification t) A hA i x hxS
  let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
  let Ω := p.probeDomain r ρ
  let R : Set (ProbeParameters r × E) := {w | w ∈ Ω ∧ HasSupportedKernel
    (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1) ((A.chart i).symm w.2))}
  have hadmissible (w : ProbeParameters r × E) (hw : w ∈ Ω) :
      ‖w.1‖ < probe.radius ∧ w.2 ∈ (A.chart i).target ∧
        ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2)).starProjection -
          (normalSpace (I := IM) F₀ x).starProjection‖ < 1 := by
    have hu : ‖w.1‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hw.1
    refine ⟨hu.trans_le hρradius, hw.2.1, ?_⟩
    exact (p.normal_gap _ hw.2.2).trans (by norm_num)
  have hclose (u : ProbeParameters r) (hu : ‖u‖ < ρ) (z : M) (hz : z ∈ p.neighborhood) :
      ‖C (u, A.chart i z) - B‖ < p.tolerance := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C (u, A.chart i z))
      (normalizedReferenceForm A hA F₀ i x hxS z) B
    have hstep := hnew u hu z hz
    have href := p.reference_variation z hz
    have hpos := p.tolerance_pos
    linarith
  have hsmall (u : ProbeParameters r) (hu : ‖u‖ < ρ) :
      (probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hxS‖ ≤
        p.tolerance / 16 := by
    apply le_trans ?_ hbudget
    exact mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu.le probe.constant_nonneg))
      (norm_nonneg _)
  have hvariation (z : M) (hz : z ∈ p.neighborhood) (j : Fin (n * (n - 1) / 2)) :
      ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxS z) ((waves (labels j)).tensor z)) -
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((waves (labels j)).tensor x)‖ ≤ p.tolerance / 16 := by
    rw [hlabels j]
    exact (p.tensor_variation z hz j).le
  have hlocal (w : ProbeParameters r × E) (hw : w ∈ R) :
      ∃ U : Set (ProbeParameters r × E), IsOpen U ∧ w ∈ U ∧
        volume (supportedProbeParameterProjection (n := n) r '' (R ∩ U)) = 0 := by
    let z := (A.chart i).symm w.2
    have hzU : z ∈ p.neighborhood := hw.1.2.2
    have hu : ‖w.1‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hw.1.1
    have hz : z ∈ A.support i := interior_subset (p.support hzU)
    have heq : (w.1, A.chart i z) = w := by
      apply Prod.ext
      · rfl
      · exact (A.chart i).right_inv hw.1.2.1
    have hwΩ : (w.1, A.chart i z) ∈ Ω := heq.symm ▸ hw.1
    obtain ⟨U, hU, hwU, _, hnull⟩ := packet.exact_probe_supported_local_null hn A hA i hxS
      p.tolerance p.tolerance_pos p.equation_stability r waves labels hlabels probe t ht htt Ω
      (p.probeDomain_open r ρ) hadmissible w.1 (hu.trans_le hρradius) z hz hwΩ hw.2
      (hclose w.1 hu z hzU) (hsmall w.1 hu) (hvariation z hzU)
    refine ⟨U, hU, heq ▸ hwU, measure_mono_null (image_mono ?_) hnull⟩
    intro v hv
    exact ⟨hv.2, hv.1.2⟩
  have hnull := avoidance_image_null_of_locally_null volume R
    (supportedProbeParameterProjection (n := n) r) hlocal
  apply measure_mono_null ?_ hnull
  rintro v ⟨u, hu, rfl⟩
  obtain ⟨z, hzU, hsupported⟩ := hu.2
  have hzS := hA.support_subset i (interior_subset (p.support hzU))
  have hzT := (A.chart i).map_source hzS
  refine ⟨(u, A.chart i z), ?_, rfl⟩
  refine ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu.1,
    hzT, ?_⟩, ?_⟩
  · change (A.chart i).symm (A.chart i z) ∈ p.neighborhood
    rw [(A.chart i).left_inv hzS]
    exact hzU
  · change HasSupportedKernel (trueSecondForm (probe.map t u) (probe.slice_smooth t u)
      ((A.chart i).symm (A.chart i z)))
    exact ((A.chart i).left_inv hzS).symm ▸ hsupported

#print axioms exists_small_probe_parameter_outside_null
#print axioms SupportedPreparedNeighborhood.probeDomain_open
#print axioms SupportedPreparedNeighborhood.exact_probe_supported_bad_parameters_null

end GlobalEmbedding.Upgrade
