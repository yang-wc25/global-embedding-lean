import Round2.SupportedJointGapUniform
import Upgrade.IncidenceSupportedAvoidance
import Upgrade.IncidencePairChartAvoidance
import Upgrade.SupportedValueProbeAvoidance

/-!
# Actual dimension-three supported-coincidence avoidance using only Qop gap

The actual equation domain is protected on the whole fixed prepared region.
Rank is invoked solely at the actual supported-coincidence zero under review.
The original local avoidance theorem and countable atlas image-null consumer
are reused; no assertion removes all supported kernels in dimension three.
-/

noncomputable section
open Function Manifold Module Set MeasureTheory
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
attribute [local instance] incidenceActualFormNormed incidenceActualFormSpace

/-- Full probes, the reference immersion and the same Qop gap give a fixed
positive ball and scale for null bad parameters of actual supported
coincidences. No spatial derivative bound for Q occurs. -/
theorem SupportedJointPreparedNeighborhood.exists_parameter_ball_scale_supportedCoincidence_null_of_gap
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx) (hn : n = 3)
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalGap probe) :
    ∃ ρ > 0, ρ ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ →
      volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < ρ ∧
        ∃ zy ∈ prep.neighborhood, HasSupportedKernel
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) zy.1) ∧
          probe.map t u zy.1 = probe.map t u zy.2}) = 0 := by
  letI : SecondCountableTopology M := bufferedAtlas_secondCountable A
  obtain ⟨ρ, hρ, hρrad, t₀, ht₀, ht₀top, hcontrol⟩ :=
    prep.exists_uniform_probe_domain_rank_of_gap hcompact himm₀ probe control labels hinj hlabels
  refine ⟨ρ, hρ, hρrad, t₀, ht₀, ht₀top, ?_⟩
  intro t ht htt
  have httop := htt.trans_le ht₀top
  let hxc := hA.support_subset i (interior_subset hx)
  let R : Set (ProbeParameters r × (M × M)) := {w | ‖w.1‖ < ρ ∧ w.2 ∈ prep.neighborhood ∧
    HasSupportedKernel (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1) w.2.1) ∧
      probe.map t w.1 w.2.1 = probe.map t w.1 w.2.2}
  have hnull : volume ((fun z : ProbeParameters r × (M × M) ↦
      probeParameterCoordinates r z.1) '' R) = 0 := by
    apply actual_pair_incidence_parameter_image_null A volume (probeParameterCoordinates r) R
    intro w hw
    have hxi := hA.support_subset i (interior_subset (prep.support w.2 hw.2.1))
    obtain ⟨j, hj⟩ := A.cover w.2.2
    have hy := A.inner_subset j hj
    let e := actualPairChart (P := ProbeParameters r) A i j
    let data := p.probeData hA i hxc probe t j
    let Ω : Set (ProbeParameters r × (E × E)) :=
      e.target ∩ e.symm ⁻¹' (Metric.ball 0 ρ ×ˢ prep.neighborhood)
    have hΩ : IsOpen Ω := e.symm.isOpen_inter_preimage
      (Metric.isOpen_ball.prod prep.neighborhood_open)
    have hwsrc : w ∈ e.source := ⟨mem_univ _, hxi, hy⟩
    have hwΩ : e w ∈ Ω := by
      refine ⟨e.map_source hwsrc, ?_⟩
      change e.symm (e w) ∈ Metric.ball 0 ρ ×ˢ prep.neighborhood
      rw [e.left_inv hwsrc]
      exact ⟨by simpa using hw.1, hw.2.1⟩
    have hcoords (z : ProbeParameters r × (E × E)) (hz : z ∈ Ω) :
        ‖z.1‖ < ρ ∧ z.2.1 ∈ (A.chart i).target ∧ z.2.2 ∈ (A.chart j).target ∧
          ((A.chart i).symm z.2.1, (A.chart j).symm z.2.2) ∈ prep.neighborhood := by
      change ((z.1 ∈ (univ : Set (ProbeParameters r)) ∧
        z.2.1 ∈ (A.chart i).target ∧ z.2.2 ∈ (A.chart j).target) ∧
        z.1 ∈ Metric.ball 0 ρ ∧
        ((A.chart i).symm z.2.1, (A.chart j).symm z.2.2) ∈ prep.neighborhood) at hz
      exact ⟨by simpa using hz.2.1, hz.1.2.1, hz.1.2.2, hz.2.2⟩
    have hactual (z : ProbeParameters r × (E × E)) (hz : z ∈ Ω) :
        actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (z.1,z.2.1) ∈ p.chart.domain ∧
        (HasSupportedKernel (trueSecondForm (probe.map t z.1) (probe.slice_smooth t z.1)
            ((A.chart i).symm z.2.1)) →
          n * (n - 1) / 2 + 2 * n ≤ finrank ℝ (fderiv ℝ data.incidence z).range) := by
      obtain ⟨hu, hz₁, hz₂, hprep⟩ := hcoords z hz
      have hh := hcontrol t ht htt z.1 hu
        ((A.chart i).symm z.2.1, (A.chart j).symm z.2.2) hprep j ((A.chart j).map_target hz₂)
      have hpoint : (z.1,A.chart i ((A.chart i).symm z.2.1),
          A.chart j ((A.chart j).symm z.2.2)) = z := by
        rw [(A.chart i).right_inv hz₁, (A.chart j).right_inv hz₂]
      have heq := congrArg (fun v : ProbeParameters r × (E × E) ↦
        finrank ℝ (fderiv ℝ data.incidence v).range) hpoint
      refine ⟨?_, fun hs ↦ (hh.2 hs).trans_eq heq⟩
      simpa only [(A.chart i).right_inv hz₁] using! hh.1
    have htargets (z : ProbeParameters r × (E × E)) (hz : z ∈ Ω) :
        z.1 ∈ Metric.ball 0 probe.radius ∧ z.2.1 ∈ (A.chart i).target ∧
          z.2.2 ∈ (A.chart data.secondChart).target := by
      obtain ⟨hu, hz₁, hz₂, _⟩ := hcoords z hz
      exact ⟨by simpa using hu.trans_le hρrad, hz₁, hz₂⟩
    have hgap (z : ProbeParameters r × (E × E)) (hz : z ∈ Ω) :
        ‖(normalSpace (I := IM) F₀ ((A.chart i).symm z.2.1)).starProjection -
          (normalSpace (I := IM) F₀ x).starProjection‖ < 1 := by
      have hg := prep.normal_gap _ (hcoords z hz).2.2.2
      exact hg.trans (by norm_num)
    have hJ : ContDiffOn ℝ ∞ data.incidence Ω := data.contDiffOn_incidence
      Metric.isOpen_ball (probe.joint_smooth t ht httop) (probe.normalIdentification_smooth t ht httop)
      htargets (fun z hz ↦ (hactual z hz).1)
    have hezero : data.incidence (e w) = 0 := by
      change data.incidence (w.1,A.chart i w.2.1,A.chart j w.2.2) = 0
      apply (data.zero_iff (w.1,A.chart i w.2.1,A.chart j w.2.2)
        (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos ht _).ne'
        (htargets _ hwΩ).2.1 (hgap _ hwΩ) (hactual _ hwΩ).1).mpr
      change HasSupportedKernel (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1)
          ((A.chart i).symm (A.chart i w.2.1))) ∧
        probe.map t w.1 ((A.chart i).symm (A.chart i w.2.1)) =
          probe.map t w.1 ((A.chart j).symm (A.chart j w.2.2))
      rw [(A.chart i).left_inv hxi, (A.chart j).left_inv hy]
      exact hw.2.2
    have hrank : 2 * n + 1 ≤ finrank ℝ (fderiv ℝ data.incidence (e w)).range := by
      have hs : HasSupportedKernel (trueSecondForm (probe.map t (e w).1)
          (probe.slice_smooth t (e w).1) ((A.chart i).symm (e w).2.1)) := by
        change HasSupportedKernel (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1)
          ((A.chart i).symm (A.chart i w.2.1)))
        rw [(A.chart i).left_inv hxi]
        exact hw.2.2.1
      have hr := (hactual _ hwΩ).2 hs
      have hbound : 2 * n + 1 ≤ n * (n - 1) / 2 + 2 * n := by rw [hn]; norm_num
      exact hbound.trans hr
    obtain ⟨W, hW, hwW, hWsub, hnullW⟩ := actual_probe_pair_local_null_of_rank
      hΩ hJ hwΩ hezero hrank
    refine ⟨i, j, W, hxi, hy, hW, hwW, ?_⟩
    apply measure_mono_null (image_mono ?_) hnullW
    intro z hz
    refine ⟨hz.1, ?_⟩
    apply (data.zero_iff z (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos ht _).ne'
      (htargets z (hWsub hz.1)).2.1 (hgap z (hWsub hz.1)) (hactual z (hWsub hz.1)).1).mpr
    exact hz.2.2.2
  apply measure_mono_null ?_ hnull
  rintro q ⟨u, hu, rfl⟩
  obtain ⟨zy, hzy, hsupp, hcoin⟩ := hu.2
  exact ⟨(u,zy), ⟨hu.1,hzy,hsupp,hcoin⟩, rfl⟩

#print axioms SupportedJointPreparedNeighborhood.exists_parameter_ball_scale_supportedCoincidence_null_of_gap
end GlobalEmbedding.Upgrade
