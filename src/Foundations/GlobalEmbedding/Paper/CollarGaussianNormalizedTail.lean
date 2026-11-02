import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Normalization and concentration of the actual Gaussian approximation kernel

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof line 520. The normalization and concentration used for global smooth approximation are
proved for the actual Gaussian kernel, including zero-dimensional Euclidean spaces.
-/

open MeasureTheory Filter Metric Set
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The actual normalized Gaussian is nonnegative, integrable, has mass one, and its mass
outside every fixed positive-radius ball tends to zero as the width tends to zero from above.

Source: Proposition `prop:collar`, proof line 520; normalization/concentration details.
The finite-dimensional Gaussian integral with b=1/ε gives the exact mass-one formula with the
source factor (π ε)^(-d/2). Its nonzero integral proves integrability. Under x=sqrt(ε)y, the
actual Jacobian times the actual width-ε kernel equals the normalized width-one kernel.
Consequently the outside mass is the integral of that integrable fixed kernel times the
indicator of δ≤norm(sqrt(ε)y). For every fixed y this indicator eventually vanishes. Dominated
convergence gives concentration, with the fixed nonnegative width-one kernel as dominator.
All identities and estimates also hold when d=0; no positive-dimension assumption is used. -/
theorem collar_gaussian_normalized_tail (d : ℕ) :
    let K : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun ε x ↦
      (Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / ε)
    (∀ ε : ℝ, 0 < ε → (∀ x, 0 ≤ K ε x) ∧ Integrable (K ε) ∧ ∫ x, K ε x = 1) ∧
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun ε : ℝ ↦ ∫ x in {x | δ ≤ ‖x‖}, K ε x) (𝓝[>] 0) (𝓝 0) := by
  let V := EuclideanSpace ℝ (Fin d)
  let K : ℝ → V → ℝ := fun ε x ↦
    (Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / ε)
  change (∀ ε : ℝ, 0 < ε → (∀ x, 0 ≤ K ε x) ∧ Integrable (K ε) ∧ ∫ x, K ε x = 1) ∧ _
  have hmass (ε : ℝ) (hε : 0 < ε) : ∫ x, K ε x = 1 := by
    have hbase := GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := V) (b := 1 / ε) (one_div_pos.mpr hε)
    have hexp : (fun x : V ↦ Real.exp (-‖x‖ ^ 2 / ε)) =
        (fun x ↦ Real.exp (-(1 / ε) * ‖x‖ ^ 2)) := by
      ext x
      congr 1
      ring
    dsimp only [K]
    rw [integral_const_mul, hexp, hbase]
    simp only [V, finrank_euclideanSpace, Fintype.card_fin, one_div, div_inv_eq_mul]
    rw [← Real.rpow_add (mul_pos Real.pi_pos hε)]
    convert Real.rpow_zero (Real.pi * ε) using 2; ring
  have hnonneg (ε : ℝ) (hε : 0 < ε) (x : V) : 0 ≤ K ε x :=
    mul_nonneg (Real.rpow_nonneg (mul_pos Real.pi_pos hε).le _) (Real.exp_pos _).le
  have hki : Integrable (K 1) := integrable_of_integral_eq_one (hmass 1 zero_lt_one)
  have hscale (ε : ℝ) (hε : 0 < ε) (x : V) :
      (Real.sqrt ε) ^ d * K ε (Real.sqrt ε • x) = K 1 x := by
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hpow : (Real.sqrt ε) ^ d = ε ^ ((d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hε.le]
      congr 1
      ring
    have he : -‖Real.sqrt ε • x‖ ^ 2 / ε = -‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, Real.sq_sqrt hε.le]
      field_simp
    dsimp only [K]
    rw [he, hpow, Real.mul_rpow Real.pi_pos.le hε.le]
    have hc : ε ^ ((d : ℝ) / 2) * ε ^ (-(d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hε]
      convert Real.rpow_zero ε using 2; ring
    calc
      _ = (ε ^ ((d : ℝ) / 2) * ε ^ (-(d : ℝ) / 2)) *
          (Real.pi ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)) := by ring
      _ = _ := by simp only [hc, one_mul, mul_one, div_one]
  refine ⟨fun ε hε ↦ ⟨hnonneg ε hε, integrable_of_integral_eq_one (hmass ε hε),
    hmass ε hε⟩, ?_⟩
  intro δ hδ
  let T : ℝ → V → ℝ := fun ε ↦ {x | δ ≤ ‖Real.sqrt ε • x‖}.indicator (K 1)
  have hset (ε : ℝ) : MeasurableSet {x : V | δ ≤ ‖Real.sqrt ε • x‖} := by
    have hsc : Continuous (fun x : V ↦ Real.sqrt ε • x) :=
      (continuous_id : Continuous (fun x : V ↦ x)).const_smul (Real.sqrt ε)
    exact measurableSet_le measurable_const hsc.norm.measurable
  have htmeas (ε : ℝ) : AEStronglyMeasurable (T ε) :=
    hki.aestronglyMeasurable.indicator (hset ε)
  have htbound (ε : ℝ) (x : V) : ‖T ε x‖ ≤ K 1 x := by
    by_cases hx : δ ≤ ‖Real.sqrt ε • x‖
    · simp [T, hx, abs_of_nonneg (hnonneg 1 zero_lt_one x)]
    · simpa [T, Set.indicator, hx] using hnonneg 1 zero_lt_one x
  have htlim (x : V) : Tendsto (fun ε : ℝ ↦ T ε x) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto (fun ε : ℝ ↦ ‖Real.sqrt ε • x‖) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero, zero_smul, norm_zero] using
        (((Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).smul_const x).norm
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖Real.sqrt ε • x‖ < δ :=
      hs.eventually (gt_mem_nhds hδ)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with ε hε
    simp [T, not_le.mpr hε]
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x, T ε x) (𝓝[>] 0) (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (K 1)
        (Eventually.of_forall htmeas)
        (Eventually.of_forall fun ε ↦ ae_of_all _ (htbound ε)) hki
        (ae_of_all _ htlim)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  let F : V → ℝ := {x | δ ≤ ‖x‖}.indicator (K ε)
  have hFset : MeasurableSet {x : V | δ ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hi := Measure.integral_comp_smul_of_nonneg volume F (Real.sqrt ε)
    (hR := hs.le)
  simp only [V, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hi
  have hmul : (Real.sqrt ε) ^ d * (∫ x, F (Real.sqrt ε • x)) = ∫ x, F x := by
    rw [hi]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hs.ne'), one_mul]
  calc
    (∫ x, T ε x) = ∫ x, (Real.sqrt ε) ^ d * F (Real.sqrt ε • x) := by
      congr 1
      ext x
      by_cases hx : δ ≤ ‖Real.sqrt ε • x‖
      · simpa [T, F, Set.indicator, hx] using (hscale ε hε x).symm
      · simp [T, F, hx]
    _ = (Real.sqrt ε) ^ d * (∫ x, F (Real.sqrt ε • x)) := integral_const_mul _ _
    _ = ∫ x, F x := hmul
    _ = ∫ x in {x | δ ≤ ‖x‖}, K ε x := integral_indicator hFset

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_gaussian_normalized_tail
