import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A single analytic inverse-square-root series on ambient operators

The operator is explicitly the binomial series at `-E`. All later construction,
smoothness and response files use this definition. The algebraic identity which
turns it into an inverse square root is proved in the construction files; none
of the regularity statements below assumes regularity of its value.
-/

noncomputable section
open Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal binomial-series value, not a separately selected square root. -/
def actualInvSqrt (E : V →L[ℝ] V) : V →L[ℝ] V :=
  (binomialSeries (V →L[ℝ] V) (-1 / 2 : ℝ)).sum (-E)

/-- The ambient direction is new normal space to old normal space. -/
def actualPolarOperator (P R : V →L[ℝ] V) : V →L[ℝ] V :=
  actualInvSqrt ((P - R) ^ 2) * P * R

theorem actualInvSqrt_eq_tsum (E : V →L[ℝ] V) :
    actualInvSqrt E = ∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • (-E) ^ n := by
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

@[simp] theorem actualInvSqrt_zero : actualInvSqrt (0 : V →L[ℝ] V) = 1 := by
  change FormalMultilinearSeries.ofScalarsSum (fun n ↦ Ring.choose (-1 / 2 : ℝ) n)
    (- (0 : V →L[ℝ] V)) = 1
  simp

/-- Scalar binomial convergence transfers to operators, also when `V` is zero
dimensional. The zero-th multilinear coefficient uses `norm_id_le`. -/
theorem binomialSeries_operator_radius_ge_one (a : ℝ) :
    1 ≤ (binomialSeries (V →L[ℝ] V) a).radius := by
  apply (binomialSeries_radius_ge_one (𝔸 := ℝ) (a := a)).trans
  apply FormalMultilinearSeries.radius_le_of_le
  intro n
  cases n with
  | zero =>
      simp only [binomialSeries, FormalMultilinearSeries.ofScalars_norm_eq_mul,
        ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero, Ring.choose_zero_right,
        norm_one, one_mul]
      exact ContinuousLinearMap.norm_id_le
  | succ n =>
      simp only [binomialSeries]
      rw [FormalMultilinearSeries.ofScalars_norm ℝ (fun n ↦ Ring.choose a n) (n + 1)]
      exact FormalMultilinearSeries.ofScalars_norm_le _ _ _ (Nat.succ_pos n)

theorem neg_mem_binomialSeries_operator_ball (E : V →L[ℝ] V) (a : ℝ)
    (hE : ‖E‖ < 1) :
    -E ∈ Metric.eball (0 : V →L[ℝ] V) (binomialSeries (V →L[ℝ] V) a).radius := by
  apply Metric.eball_subset_eball (binomialSeries_operator_radius_ge_one a)
  rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
  simpa using hE

theorem summable_norm_actualInvSqrt (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    Summable (fun n : ℕ ↦ ‖Ring.choose (-1 / 2 : ℝ) n • (-E) ^ n‖) := by
  simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq] using
    (binomialSeries (V →L[ℝ] V) (-1 / 2 : ℝ)).summable_norm_apply
      (neg_mem_binomialSeries_operator_ball E _ hE)

variable [CompleteSpace V]

theorem analyticAt_actualInvSqrt (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    AnalyticAt ℝ actualInvSqrt E := by
  have hp := (binomialSeries (V →L[ℝ] V) (-1 / 2 : ℝ)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (binomialSeries_operator_radius_ge_one (-1 / 2 : ℝ)))
  exact (hp.analyticAt_of_mem (neg_mem_binomialSeries_operator_ball E _ hE)).comp
    (analyticAt_id.neg)

theorem contDiffAt_actualInvSqrt (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    ContDiffAt ℝ ∞ actualInvSqrt E :=
  (analyticAt_actualInvSqrt E hE).contDiffAt

theorem contDiffOn_actualInvSqrt :
    ContDiffOn ℝ ∞ (actualInvSqrt (V := V)) (Metric.ball 0 1) := by
  intro E hE
  exact (contDiffAt_actualInvSqrt E (by simpa using hE)).contDiffWithinAt

theorem norm_sub_sq_lt_one (P R : V →L[ℝ] V) (hPR : ‖P - R‖ < 1) :
    ‖(P - R) ^ 2‖ < 1 := by
  have h : ‖(P - R) ^ 2‖ ≤ ‖P - R‖ ^ 2 := by
    simpa only [pow_two] using norm_mul_le (P - R) (P - R)
  have hnonneg := norm_nonneg (P - R)
  nlinarith

theorem contDiffAt_actualPolarPair (p : (V →L[ℝ] V) × (V →L[ℝ] V))
    (hp : ‖p.1 - p.2‖ < 1) :
    ContDiffAt ℝ ∞ (fun q : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
      actualPolarOperator q.1 q.2) p := by
  have he : ContDiffAt ℝ ∞ (fun q : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
      (q.1 - q.2) ^ 2) p := (contDiffAt_fst.sub contDiffAt_snd).pow 2
  exact ((contDiffAt_actualInvSqrt _ (norm_sub_sq_lt_one _ _ hp)).comp p he).mul
    contDiffAt_fst |>.mul contDiffAt_snd

theorem exists_actualInvSqrt_derivative_bound [FiniteDimensional ℝ V] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : V →L[ℝ] V, ‖E‖ ≤ (1 / 2 : ℝ) →
      ‖fderiv ℝ actualInvSqrt E‖ ≤ C := by
  have hc := contDiffOn_actualInvSqrt (V := V) |>.continuousOn_fderiv_of_isOpen
    Metric.isOpen_ball (by simp)
  have hsub : Metric.closedBall (0 : V →L[ℝ] V) (1 / 2 : ℝ) ⊆ Metric.ball 0 1 := by
    intro E hE
    simp only [Metric.mem_closedBall, dist_zero_right] at hE
    simpa using (hE.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V →L[ℝ] V) (1 / 2 : ℝ)).exists_bound_of_continuousOn
    (hc.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun E hE ↦ ?_⟩
  exact (hC E (by simpa using hE)).trans (le_max_left _ _)

end GlobalEmbedding.NormalPolar
