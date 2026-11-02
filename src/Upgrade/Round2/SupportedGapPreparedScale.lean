import Upgrade.SupportedPreparedAvoidance
import Round2.ProbeNormalGap

/-!
# Supported-kernel scale selection using only the actual normal gap

For n≥4 the already proved supported incidence rank is furnished by parameter
columns alone.  Its prepared null theorem therefore needs actual form closeness
but no quantitative spatial derivative of the normal identification.  The
original full probe errors and the same Qop's zeroth-order gap provide exactly
that closeness.  This removes the unused DQ premise from this branch without
changing its actual supported set, local equations, rank proof or null theorem.
-/

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The same fixed neighborhood and same literal supported bad parameters as
the original prepared theorem, now with only the actual zero-order Qop gap.
The parameter ball is selected before the scale. -/
theorem SupportedPreparedNeighborhood.exists_parameter_ball_scale_supported_null_of_gap
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {packet : SupportedLocalWavePacket F₀ hF₀ x y} {i : Fin A.count}
    {hx : x ∈ interior (A.support i)}
    (p : SupportedPreparedNeighborhood A hA packet i hx) (hn : 4 ≤ n)
    (r : ℕ) (waves : Fin r → LocalLegalWave F₀ hF₀)
    (labels : Fin (n * (n - 1) / 2) → Fin r)
    (hlabels : ∀ j, waves (labels j) = packet.waves j)
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalGap probe) :
    ∃ ρ > 0, ρ ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ →
      volume (probeParameterCoordinates r '' {u : ProbeParameters r | ‖u‖ < ρ ∧
        ∃ z ∈ p.neighborhood, HasSupportedKernel
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z)}) = 0 := by
  let hxS := hA.support_subset i (interior_subset hx)
  let K := ‖probeAtlasNormalizationSquare A hA i x hxS‖
  have hK : 0 ≤ K := norm_nonneg _
  have hη : Tendsto (fun t ↦ probe.etaB t * K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using probe.etaB_tendsto.mul_const K
  obtain ⟨ρ₀, hρ₀, tB, htB, hraw⟩ := finite_probe_parameter_ball_then_scale
    (ι := Unit) (U := ℝ) (fun _ t ↦ probe.etaB t * K)
    (fun _ ↦ probe.constant * K) (fun _ ↦ p.tolerance / 16)
    (fun _ ↦ hη) (fun _ ↦ div_pos p.tolerance_pos (by norm_num))
  let ρ := min (ρ₀ / 2) (probe.radius / 2)
  have hρ : 0 < ρ := lt_min (half_pos hρ₀) (half_pos probe.radius_pos)
  have hρsmall : ρ < ρ₀ := (min_le_left _ _).trans_lt (half_lt_self hρ₀)
  have hρradius : ρ ≤ probe.radius :=
    (min_le_right _ _).trans (half_le_self probe.radius_pos.le)
  obtain ⟨tF, htF, htFthreshold, hform⟩ :=
    control.eventually_actual_form_close hA hcompact i x hxS
      (show 0 < p.tolerance / 2 by exact half_pos p.tolerance_pos)
  refine ⟨ρ, hρ, hρradius, min tB tF, lt_min htB htF,
    (min_le_right _ _).trans htFthreshold, ?_⟩
  intro t ht htt
  have htBt : t < tB := htt.trans_le (min_le_left _ _)
  have htFt : t < tF := htt.trans_le (min_le_right _ _)
  have httop : t < probe.threshold := htFt.trans_le htFthreshold
  have hrawρ := hraw t ht htBt ρ
    (by simpa only [Real.norm_eq_abs, abs_of_pos hρ] using hρsmall) ()
  have hbudget : (probe.etaB t + probe.constant * ρ) * K ≤ p.tolerance / 16 := by
    have hηnonneg : 0 ≤ probe.etaB t * K := mul_nonneg (probe.etaB_nonneg t) hK
    have hCnonneg : 0 ≤ probe.constant * K := mul_nonneg probe.constant_nonneg hK
    simp only [abs_of_nonneg hηnonneg, abs_of_nonneg hCnonneg,
      Real.norm_eq_abs, abs_of_pos hρ] at hrawρ
    have heq : (probe.etaB t + probe.constant * ρ) * K =
        probe.etaB t * K + (probe.constant * K) * ρ := by ring
    rw [heq]
    exact hrawρ.le
  apply p.exact_probe_supported_bad_parameters_null hn r waves labels hlabels probe
    t ht httop ρ hρ hρradius hbudget
  intro u hu z hz
  exact (hform t ht htFt u (hu.trans_le hρradius) z
    (interior_subset (p.support hz))).le

end GlobalEmbedding.Upgrade
