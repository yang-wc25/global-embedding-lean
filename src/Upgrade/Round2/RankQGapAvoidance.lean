import Round2.RankQGapRank
import Upgrade.RankQPreparedChartGeometry
import Upgrade.IncidenceSupportedAvoidance
import Upgrade.SupportedValueProbeAvoidance

/-!
# Actual rank-q coincidence avoidance on one fixed prepared neighborhood

Full probes and the zeroth-order gap of the same chosen normal
identification give one parameter ball and one scale.  For every admitted
scale, the parameters producing an actual rank-at-most-q coincidence inside
the unchanged prepared source neighborhood form a null set.  The rank at actual zeros is
derived from actual Schur/paired/tangent columns without a spatial DQ bound, and the accepted avoidance
theorem is applied to the same literal actual incidence.
-/
noncomputable section
open Function Manifold Module Set MeasureTheory
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm rankQActualDerivativeNorm

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private theorem rankQ_gap_prepared_bad_parameters_null
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (rho : ℝ) (hrho : rho ≤ probe.radius) :
    let hxc := hA.support_subset i (interior_subset hx)
    (∀ u : ProbeParameters r, ‖u‖ < rho → ∀ zy ∈ prep.neighborhood,
      (rankQBlockA (rankQActualReference F₀ hF₀ x)
        (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1))).IsInvertible ∧
      (rankQSchur (rankQActualReference F₀ hF₀ x)
        (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1)) = 0 →
      ∀ j : Fin A.count, zy.2 ∈ (A.chart j).source →
        2 * n + 1 ≤ finrank ℝ (fderiv ℝ
          (actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
            (probe.normalIdentification t) A hA i j x hxc
            (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)))
          (u,A.chart i zy.1,A.chart j zy.2)).range)) →
    volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < rho ∧
      ∃ zy ∈ prep.neighborhood,
        finrank ℝ (trueSecondForm (probe.map t u) (probe.slice_smooth t u) zy.1).range ≤
          n * (n - 1) / 2 ∧ probe.map t u zy.1 = probe.map t u zy.2}) = 0 := by
  intro hxc hprotected
  letI : SecondCountableTopology M := bufferedAtlas_secondCountable A
  let R : Set (ProbeParameters r × (M × M)) := {w | ‖w.1‖ < rho ∧
    w.2 ∈ prep.neighborhood ∧
    finrank ℝ (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1) w.2.1).range ≤
      n * (n - 1) / 2 ∧ probe.map t w.1 w.2.1 = probe.map t w.1 w.2.2}
  have hsigma : t ^ ((44 : ℝ) / 5) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have ha : t ^ ((56 : ℝ) / 5) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hnull : volume ((fun w : ProbeParameters r × (M × M) ↦
      probeParameterCoordinates r w.1) '' R) = 0 := by
    apply actual_pair_incidence_parameter_image_null A volume (probeParameterCoordinates r) R
    intro w hw
    have hfirst := hA.support_subset i
      (interior_subset (prep.principal.support w.2 (prep.subset_principal hw.2.1)))
    obtain ⟨j, hj⟩ := A.cover w.2.2
    have hsecond := A.inner_subset j hj
    let Ω := prep.coordinateDomain (r := r) rho j
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc
      (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
    have hJ := prep.probe_contDiffOn_coordinateDomain probe t ht htt rho hrho j
      (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
      (fun u hu zy hzy ↦ (hprotected u hu zy hzy).1)
    have hwΩ : (w.1,A.chart i w.2.1,A.chart j w.2.2) ∈ Ω :=
      prep.actual_point_mem_coordinateDomain rho j w.1 hw.1 w.2 hw.2.1 hsecond
    have hzero : J (w.1,A.chart i w.2.1,A.chart j w.2.2) = 0 := by
      apply (prep.probe_zero_iff_coordinateDomain himm hrank probe t rho j
        (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)) hsigma ha _ hwΩ
        (hprotected w.1 hw.1 w.2 hw.2.1).1).mpr
      rw [(A.chart i).left_inv hfirst, (A.chart j).left_inv hsecond]
      exact hw.2.2
    have hfirstZero := congrArg Prod.fst hzero
    change (t ^ ((44 : ℝ) / 5))⁻¹ • rankQSchur (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hxc (w.1,A.chart i w.2.1)) = 0 at hfirstZero
    have hschur := (smul_eq_zero.mp hfirstZero).resolve_left (inv_ne_zero hsigma)
    have hjoint := (hprotected w.1 hw.1 w.2 hw.2.1).2 hschur j hsecond
    obtain ⟨W, hW, hwW, hWsub, hWnull⟩ := actual_probe_pair_local_null_of_rank
      (n := n) (r := r) (prep.coordinateDomain_open rho j) hJ hwΩ hzero hjoint
    refine ⟨i, j, W, hfirst, hsecond, hW, hwW, ?_⟩
    apply measure_mono_null (image_mono ?_) hWnull
    intro z hz
    have hm := (prep.mem_coordinateDomain_iff rho j z).mp (hWsub hz.1)
    have hb := (hprotected z.1 hm.1
      ((A.chart i).symm z.2.1, (A.chart j).symm z.2.2) hm.2.2.2).1
    have hb' : (rankQBlockA (rankQActualReference F₀ hF₀ x)
        (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (z.1,z.2.1))).IsInvertible := by
      simpa only [(A.chart i).right_inv hm.2.1] using hb
    refine ⟨hz.1, ?_⟩
    apply (prep.probe_zero_iff_coordinateDomain himm hrank probe t rho j
      (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)) hsigma ha z (hWsub hz.1) hb').mpr
    exact hz.2.2.2
  apply measure_mono_null ?_ hnull
  rintro v ⟨u, hu, rfl⟩
  obtain ⟨zy, hzy, hbad⟩ := hu.2
  exact ⟨(u,zy), ⟨hu.1,hzy,hbad⟩, rfl⟩

/-- Complete downstream rank-q coincidence nullity from the full original
probe estimates and the explicitly recorded chosen-normal-gap dependency.
Neither the required incidence rank nor a null bad set is assumed. -/
theorem RankQSchurPreparedNeighborhood.exists_parameter_ball_scale_rankQCoincidence_null_of_gap
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalGap probe)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Injective labels)
    (hlabels : ∀ l, waves (labels l) = p.waves l.1) :
    ∃ rho > 0, rho ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ →
      volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < rho ∧
        ∃ zy ∈ prep.neighborhood,
          finrank ℝ (trueSecondForm (probe.map t u) (probe.slice_smooth t u) zy.1).range ≤
            n * (n - 1) / 2 ∧ probe.map t u zy.1 = probe.map t u zy.2}) = 0 := by
  obtain ⟨rho, hrho, hrhoBound, tau, htau, htauBound, hprotected⟩ :=
    prep.exists_probe_ball_scale_rank_at_zeros_from_gap hcompact probe control himm labels hinj hlabels
  refine ⟨rho, hrho, hrhoBound, tau, htau, htauBound, ?_⟩
  intro t ht htt
  exact rankQ_gap_prepared_bad_parameters_null prep himm hrank probe t ht
    (htt.trans_le htauBound) rho hrhoBound (hprotected t ht htt)

#print axioms RankQSchurPreparedNeighborhood.exists_parameter_ball_scale_rankQCoincidence_null_of_gap
end GlobalEmbedding.Upgrade
