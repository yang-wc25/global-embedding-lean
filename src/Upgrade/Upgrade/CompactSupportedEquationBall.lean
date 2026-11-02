import Upgrade.SupportedEquationStability

/-!
# A fixed derivative ball for the actual supported defining chart

This is continuity of the already accepted chart's actual defining equation.
It is separate from weight simulation: its derivative error is multiplied
only by the fixed actual tensor bound, never by returned-weight coefficients.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {ambient locus : Set X} {B : X}

structure PreparedSupportedEquationBall
    (chart : SupportedLocusLocalEquations ambient locus B) (delta : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  spec : ∀ C : X, ‖C - B‖ < radius →
    C ∈ chart.domain ∧ ContDiffAt ℝ ∞ chart.equation C ∧
    ‖fderiv ℝ chart.equation C - fderiv ℝ chart.equation B‖ < delta ∧
    ‖fderiv ℝ chart.equation C‖ ≤ ‖fderiv ℝ chart.equation B‖ + delta

theorem exists_prepared_supported_equation_ball
    (chart : SupportedLocusLocalEquations ambient locus B) {delta : ℝ} (hdelta : 0 < delta) :
    Nonempty (PreparedSupportedEquationBall chart delta) := by
  have hdf : ContinuousAt (fderiv ℝ chart.equation) B :=
    (chart.contDiffOn_equation.contDiffAt
      (chart.isOpen_domain.mem_nhds chart.mem_domain)).continuousAt_fderiv (by simp)
  have hnear : ∀ᶠ C in 𝓝 B,
      ‖fderiv ℝ chart.equation C - fderiv ℝ chart.equation B‖ < delta := by
    exact (hdf.sub continuousAt_const).norm.eventually_lt_const (by
      change ‖fderiv ℝ chart.equation B - fderiv ℝ chart.equation B‖ < delta
      simpa only [sub_self, norm_zero] using hdelta)
  have hdom : ∀ᶠ C in 𝓝 B, C ∈ chart.domain := chart.isOpen_domain.mem_nhds chart.mem_domain
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff.mp (hdom.and hnear)
  refine ⟨⟨rho, hrho, ?_⟩⟩
  intro C hC
  have h := hball (by simpa only [dist_eq_norm] using hC)
  refine ⟨h.1, chart.contDiffOn_equation.contDiffAt (chart.isOpen_domain.mem_nhds h.1), h.2, ?_⟩
  have htri := norm_le_norm_sub_add (fderiv ℝ chart.equation C) (fderiv ℝ chart.equation B)
  linarith

end GlobalEmbedding.Upgrade
