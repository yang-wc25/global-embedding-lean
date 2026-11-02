import Upgrade.SupportedValueProbeAvoidance
import Upgrade.CompactOriginalC2Geometry
import Upgrade.CompactProbeScales

/-!
# One parameter ball and scale for the actual final value operation

The prepared neighborhood, unweighted frame and positive margin precede the
global wave list and probes. The returned weights only scale the genuine
global remainder constants. Original C² closeness controls the literal new
normal projector, so this value-only operation needs no selected-normal
identification control. No incidence rank, error bound or good parameter is
left as an input to the final quantified null-set conclusion.
-/

noncomputable section
open Bundle Manifold Set Module Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Full actual probes imply null exceptional parameters on the same prepared
value neighborhood, for one positive parameter ball followed by one small
scale. Every projector and remainder smallness condition is proved here. -/
theorem ValuePreparedNeighborhood.exists_parameter_ball_scale_value_null
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ z, ∃ i, z ∈ A.support i) (hdim : 2 ≤ n)
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : LegalValueWavePacket F₀ hF₀ x y (n + 1)} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : ValuePreparedNeighborhood A hA packet i hx)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z)) (hphase : PhaseRegular F₀ hF₀)
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : Fin (n + 1) → Fin r) (hlabels : ∀ j, waves (labels j) = packet.waves j)
    (probe : ExactProbeFamily F₀ hF₀ A waves) :
    ∃ ρ > 0, ρ ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ →
      volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < ρ ∧
        ∃ z ∈ p.neighborhood, probe.map t u z.1 = probe.map t u z.2}) = 0 := by
  classical
  let K := 1 + ∑ l : Fin (n + 1), ‖(packet.waves l).value x‖
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKbound (l : Fin (n + 1)) : ‖(packet.waves l).value x‖ ≤ K := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) ↦
      norm_nonneg ((packet.waves j).value x)) (Finset.mem_univ l)
    dsimp only [K]
    linarith
  let δ := p.tolerance / (4 * K)
  have hδ : 0 < δ := div_pos p.tolerance_pos (by positivity)
  have hδK : δ * K = p.tolerance / 4 := by dsimp only [δ]; field_simp
  obtain ⟨e, he, hnormal⟩ := exists_originalC2_normal_and_form_budget
    A hA hcompact hcover hdim F₀ hF₀ himm hphase hδ
  obtain ⟨tC, htC, htCthreshold, hclose⟩ := probe.eventually_originalC2_small he
  have hη (l : Fin (n + 1)) : Tendsto
      (fun t ↦ probe.weight (labels l) ^ 2 * probe.etaV t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using probe.etaV_tendsto.const_mul (probe.weight (labels l) ^ 2)
  obtain ⟨ρ₀, hρ₀, tV, htV, hraw⟩ := finite_probe_parameter_ball_then_scale
    (U := ℝ) (fun l t ↦ probe.weight (labels l) ^ 2 * probe.etaV t)
    (fun l ↦ probe.weight (labels l) ^ 2 * probe.constant) (fun _ ↦ p.tolerance / 2)
    hη (fun _ ↦ half_pos p.tolerance_pos)
  let ρ := min (ρ₀ / 2) (probe.radius / 2)
  have hρ : 0 < ρ := lt_min (half_pos hρ₀) (half_pos probe.radius_pos)
  have hρsmall : ρ < ρ₀ := (min_le_left _ _).trans_lt (half_lt_self hρ₀)
  have hρradius : ρ ≤ probe.radius := (min_le_right _ _).trans (half_le_self probe.radius_pos.le)
  refine ⟨ρ, hρ, hρradius, min tV tC, lt_min htV htC,
    (min_le_right _ _).trans htCthreshold, ?_⟩
  intro t ht htt
  have htVt : t < tV := htt.trans_le (min_le_left _ _)
  have htCt : t < tC := htt.trans_le (min_le_right _ _)
  have httop : t < probe.threshold := htCt.trans_le htCthreshold
  have hbudget (l : Fin (n + 1)) :
      probe.weight (labels l) ^ 2 * (probe.etaV t + probe.constant * ρ) ≤ p.tolerance / 2 := by
    have hr := hraw t ht htVt ρ
      (by simpa only [Real.norm_eq_abs, abs_of_pos hρ] using hρsmall) l
    have hηnonneg := mul_nonneg (sq_nonneg (probe.weight (labels l))) (probe.etaV_nonneg t)
    have hCnonneg := mul_nonneg (sq_nonneg (probe.weight (labels l))) probe.constant_nonneg
    simp only [abs_of_nonneg hηnonneg, abs_of_nonneg hCnonneg,
      Real.norm_eq_abs, abs_of_pos hρ] at hr
    calc
      _ = probe.weight (labels l) ^ 2 * probe.etaV t +
          (probe.weight (labels l) ^ 2 * probe.constant) * ρ := by ring
      _ ≤ p.tolerance / 2 := hr.le
  apply p.exact_probe_value_bad_parameters_null himm r waves labels hlabels probe t ht httop
    ρ hρradius hbudget
  intro u hu z hz l
  have huProbe : ‖u‖ < probe.radius := hu.trans_le hρradius
  have hgap := (hnormal (probe.map t u) (probe.slice_smooth t u)
    (hclose t ht htCt u huProbe)).1 z.1
  let v := (packet.waves l).value x
  let Pnew := (normalSpace (I := IM) (probe.map t u) z.1).starProjection
  let Pold := (normalSpace (I := IM) F₀ z.1).starProjection
  have hnewold : ‖Pnew v - Pold v‖ ≤ p.tolerance / 4 := by
    calc
      _ = ‖(Pnew - Pold) v‖ := rfl
      _ ≤ ‖Pnew - Pold‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * K := mul_le_mul hgap.le (hKbound l) (norm_nonneg _) hδ.le
      _ = p.tolerance / 4 := hδK
  have hold := (p.old_normal_variation z hz l).le
  have htotal := (norm_sub_le_norm_sub_add_norm_sub (Pnew v) (Pold v) v).trans
    (add_le_add hnewold hold)
  exact htotal.trans (by linarith [p.tolerance_pos])

#print axioms ValuePreparedNeighborhood.exists_parameter_ball_scale_value_null

end GlobalEmbedding.Upgrade
