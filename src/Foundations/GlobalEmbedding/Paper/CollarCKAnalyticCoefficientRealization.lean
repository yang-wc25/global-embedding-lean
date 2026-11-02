import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Actual analytic sums of finite coordinate coefficient arrays

Source: Gantumur, Math580 notes2, Theorem18, convergence and differentiation step, pp9–10.
DAG: `collar-ck-analytic-coordinate-series`. W5 owns only analytic realization.
These generic coordinate arrays do not redefine W3's actual formal PDE or solution.
-/

noncomputable section
open scoped Topology ENNReal NNReal
open Set
namespace GlobalEmbedding.Paper

variable {σ F : Type*} [Fintype σ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual multilinear monomial for a finite coordinate word and its vector coefficient. -/
def collarCKCoordinateMonomial {k : ℕ} (w : Fin k → σ) (c : F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ σ → ℝ) F :=
  (ContinuousMultilinearMap.mkPiRing ℝ (Fin k) c).compContinuousLinearMap
    (fun i ↦ ContinuousLinearMap.proj (w i))

omit [Fintype σ] in
/-- Evaluate the genuine coordinate monomial, with each input slot retained separately. -/
theorem collarCKCoordinateMonomial_apply {k : ℕ} (w : Fin k → σ) (c : F)
    (z : Fin k → σ → ℝ) :
    collarCKCoordinateMonomial w c z = (∏ i, z i (w i)) • c := by
  simp [collarCKCoordinateMonomial, ContinuousMultilinearMap.mkPiRing_apply]

/-- Coordinate projections have norm at most one, so a monomial costs only its coefficient norm.
This includes the constant degree-zero term. -/
theorem collarCKCoordinateMonomial_norm_le {k : ℕ} (w : Fin k → σ) (c : F) :
    ‖collarCKCoordinateMonomial w c‖ ≤ ‖c‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg c)
  intro z
  rw [collarCKCoordinateMonomial_apply, norm_smul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦ norm_le_pi_norm (z i) (w i)))
    (norm_nonneg c)

/-- The actual homogeneous multilinear coefficients obtained by finite coordinate summation. -/
def collarCKCoordinateSeries (a : ∀ k : ℕ, (Fin k → σ) → F) :
    FormalMultilinearSeries ℝ (σ → ℝ) F :=
  fun k ↦ ∑ w : Fin k → σ, collarCKCoordinateMonomial w (a k w)

/-- Diagonal evaluation is exactly the genuine finite sum of coordinate monomials. -/
theorem collarCKCoordinateSeries_apply (a : ∀ k : ℕ, (Fin k → σ) → F)
    (k : ℕ) (z : σ → ℝ) :
    collarCKCoordinateSeries a k (fun _ ↦ z) = ∑ w : Fin k → σ, (∏ i, z (w i)) • a k w := by
  simp [collarCKCoordinateSeries, collarCKCoordinateMonomial_apply]

/-- The homogeneous operator norm is bounded by the sum of the original coefficient norms. -/
theorem collarCKCoordinateSeries_norm_le (a : ∀ k : ℕ, (Fin k → σ) → F) (k : ℕ) :
    ‖collarCKCoordinateSeries a k‖ ≤ ∑ w : Fin k → σ, ‖a k w‖ := by
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun w _ ↦ collarCKCoordinateMonomial_norm_le w (a k w))

/-- Absolute summability of the actual coordinate coefficients bounds the joint convergence
radius. It is an intermediate hypothesis, to be obtained from the genuine scalar majorant. -/
theorem collarCKCoordinateSeries_radius (a : ∀ k : ℕ, (Fin k → σ) → F) (r : NNReal)
    (ha : Summable (fun k ↦ (∑ w : Fin k → σ, ‖a k w‖) * (r : ℝ) ^ k)) :
    (r : ℝ≥0∞) ≤ (collarCKCoordinateSeries a).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  exact Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg k))
    (fun k ↦ mul_le_mul_of_nonneg_right (collarCKCoordinateSeries_norm_le a k)
      (pow_nonneg r.coe_nonneg k)) ha

/-- A genuinely summable coordinate array defines an actual jointly analytic function and
admits lawful termwise Frechet differentiation throughout the same positive joint ball.
The function is the actual infinite sum, with no analytic solution supplied as input. -/
theorem collarCKCoordinateSeries_realization [CompleteSpace F]
    (a : ∀ k : ℕ, (Fin k → σ) → F) (r : NNReal) (hr : 0 < r)
    (ha : Summable (fun k ↦ (∑ w : Fin k → σ, ‖a k w‖) * (r : ℝ) ^ k)) :
    HasFPowerSeriesOnBall (collarCKCoordinateSeries a).sum
      (collarCKCoordinateSeries a) 0 r ∧
    AnalyticOnNhd ℝ (collarCKCoordinateSeries a).sum (Metric.eball 0 (r : ℝ≥0∞)) ∧
    ∀ z, ‖z‖ₑ < (r : ℝ≥0∞) →
      HasFDerivAt (collarCKCoordinateSeries a).sum
        ((collarCKCoordinateSeries a).derivSeries.sum z) z := by
  have hrad := collarCKCoordinateSeries_radius a r ha
  have hpos : (0 : ℝ≥0∞) < r := ENNReal.coe_pos.mpr hr
  have hp := ((collarCKCoordinateSeries a).hasFPowerSeriesOnBall
    (hpos.trans_le hrad)).mono hpos hrad
  exact ⟨hp, hp.analyticOnNhd, fun z hz ↦
    (collarCKCoordinateSeries a).hasFDerivAt_sum (hz.trans_le hrad)⟩

omit [NormedSpace ℝ F] in
/-- A geometric bound on the genuine coordinate coefficients gives absolute joint
summability whenever the finite coordinate count times the weighted ratio is less than one. -/
theorem collarCKCoordinateSeries_summable_of_geometric
    (a : ∀ k : ℕ, (Fin k → σ) → F) (M s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ k w, ‖a k w‖ ≤ M * s ^ k) (r : NNReal)
    (hratio : (Fintype.card σ : ℝ) * s * (r : ℝ) < 1) :
    Summable (fun k ↦ (∑ w : Fin k → σ, ‖a k w‖) * (r : ℝ) ^ k) := by
  have hratio0 : 0 ≤ (Fintype.card σ : ℝ) * s * (r : ℝ) := by positivity
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (Finset.sum_nonneg fun w _ ↦ norm_nonneg _) (by positivity))
    (fun k ↦ ?_)
    ((summable_geometric_of_lt_one hratio0 hratio).mul_left M)
  calc
    (∑ w : Fin k → σ, ‖a k w‖) * (r : ℝ) ^ k ≤
        ((Fintype.card σ : ℝ) ^ k * (M * s ^ k)) * (r : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow] using Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ ha k w)
    _ = M * ((Fintype.card σ : ℝ) * s * (r : ℝ)) ^ k := by
      rw [mul_pow, mul_pow]
      ring

/-- Genuine geometric coefficient bounds construct one positive joint radius and the actual
analytic sum with exact expansion and termwise differentiation. No convergent sum or analytic
map is supplied; the finite coordinate count is explicitly included in the chosen radius. -/
theorem collarCKCoordinateSeries_realization_of_geometric [CompleteSpace F]
    (a : ∀ k : ℕ, (Fin k → σ) → F) (M s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ k w, ‖a k w‖ ≤ M * s ^ k) :
    ∃ r : NNReal, 0 < r ∧
      HasFPowerSeriesOnBall (collarCKCoordinateSeries a).sum
        (collarCKCoordinateSeries a) 0 r ∧
      AnalyticOnNhd ℝ (collarCKCoordinateSeries a).sum (Metric.eball 0 (r : ℝ≥0∞)) ∧
      ∀ z, ‖z‖ₑ < (r : ℝ≥0∞) →
        HasFDerivAt (collarCKCoordinateSeries a).sum
          ((collarCKCoordinateSeries a).derivSeries.sum z) z := by
  let q : ℝ := (Fintype.card σ : ℝ) * s
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) hs
  have hd : 0 < 2 * (q + 1) := by positivity
  let r : NNReal := ⟨1 / (2 * (q + 1)), le_of_lt (one_div_pos.mpr hd)⟩
  have hr : 0 < r := one_div_pos.mpr hd
  have hratio : (Fintype.card σ : ℝ) * s * (r : ℝ) < 1 := by
    change q * (1 / (2 * (q + 1))) < 1
    rw [mul_one_div]
    exact (div_lt_one hd).mpr (by linarith)
  exact ⟨r, hr, collarCKCoordinateSeries_realization a r hr
    (collarCKCoordinateSeries_summable_of_geometric a M s hs ha r hratio)⟩

/-- If every pure-spatial coefficient vanishes, the genuine sum vanishes on the whole
initial hyperplane. Each remaining monomial has an actual zero time-coordinate factor. -/
theorem collarCKCoordinateSeries_initial_hyperplane [CompleteSpace F]
    (a : ∀ k : ℕ, (Fin k → σ) → F) (time : σ)
    (ha : ∀ k w, (∀ i, w i ≠ time) → a k w = 0)
    (z : σ → ℝ) (hz : z time = 0) :
    (collarCKCoordinateSeries a).sum z = 0 := by
  have hterm (k : ℕ) : collarCKCoordinateSeries a k (fun _ ↦ z) = 0 := by
    rw [collarCKCoordinateSeries_apply]
    apply Finset.sum_eq_zero
    intro w _
    by_cases ht : ∃ i, w i = time
    · obtain ⟨i, hi⟩ := ht
      have hprod : (∏ j, z (w j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hz])
      rw [hprod, zero_smul]
    · rw [ha k w (by simpa only [not_exists] using ht), smul_zero]
  change (∑' k, collarCKCoordinateSeries a k (fun _ ↦ z)) = 0
  simp only [hterm, tsum_zero]

#print axioms collarCKCoordinateMonomial
#print axioms collarCKCoordinateMonomial_apply
#print axioms collarCKCoordinateMonomial_norm_le
#print axioms collarCKCoordinateSeries
#print axioms collarCKCoordinateSeries_apply
#print axioms collarCKCoordinateSeries_norm_le
#print axioms collarCKCoordinateSeries_radius
#print axioms collarCKCoordinateSeries_realization
#print axioms collarCKCoordinateSeries_summable_of_geometric
#print axioms collarCKCoordinateSeries_realization_of_geometric
#print axioms collarCKCoordinateSeries_initial_hyperplane

end GlobalEmbedding.Paper
