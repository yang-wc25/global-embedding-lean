import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# One parameter ball and one scale for the actual rank-q errors

Only the two original probe remainder moduli and the actual value/second-form
scales occur. All finite geometric and returned-weight constants are fixed
before this choice. The source geometry and the cover are not shrunk here.
-/
noncomputable section
open Filter
open scoped Topology
namespace GlobalEmbedding.Upgrade

private theorem rankQ_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun t : ℝ ↦ t ^ q) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_rpow_const (q := q) hq.le).tendsto (0 : ℝ)
  simpa only [Real.zero_rpow hq.ne'] using
    h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)

/-- Positive response bounds can be met simultaneously without changing any
previously selected spatial neighborhood. The scalar s is the parameter norm,
so this choice is independent of the eventual parameter dimension. -/
theorem rankQ_exists_probe_response_ball_scale
    (etaB etaV : ℝ → ℝ) (hB : Tendsto etaB (𝓝[>] 0) (𝓝 0))
    (hV : Tendsto etaV (𝓝[>] 0) (𝓝 0))
    (hBn : ∀ t, 0 ≤ etaB t) (hVn : ∀ t, 0 ≤ etaV t)
    (radius threshold eps amp derivative frame constant source jet : ℝ)
    (hradius : 0 < radius) (hthreshold : 0 < threshold) (heps : 0 < eps)
    (hamp : 0 < amp) (hderivative : 0 ≤ derivative) (hframe : 0 ≤ frame)
    (hconstant : 0 ≤ constant) (hsource : 0 ≤ source) (hjet : 0 ≤ jet) :
    ∃ rho > 0, rho ≤ radius ∧ ∃ t₀ > 0, t₀ ≤ threshold ∧
      ∀ t, 0 < t → t < t₀ → ∀ s, 0 ≤ s → s < rho →
        amp * max (4 * derivative * ((etaB t + constant * s) * frame))
          (4 * (etaV t + constant * s)) ≤ eps / 4 ∧
        max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| * source)
          (jet * t ^ ((44 : ℝ) / 5) + eps / 4) ≤ eps := by
  let M := 4 * amp * max (derivative * frame) 1
  have hM : 0 < M := mul_pos (mul_pos (by norm_num) hamp)
    ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_right _ _))
  let d := eps / (8 * (M + 1))
  have hd : 0 < d := div_pos heps (by positivity)
  let rho := min radius (d / (constant + 1))
  have hrho : 0 < rho := lt_min hradius (div_pos hd (by positivity))
  have he : Tendsto (fun t ↦ max (etaB t) (etaV t)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [max_self] using hB.max hV
  have hs : Tendsto (fun t : ℝ ↦ t ^ ((12 : ℝ) / 5) * source) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using (rankQ_rpow_tendsto_zero (by norm_num : (0 : ℝ) < 12 / 5)).mul_const source
  have hj : Tendsto (fun t : ℝ ↦ jet * t ^ ((44 : ℝ) / 5)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (rankQ_rpow_tendsto_zero (by norm_num : (0 : ℝ) < 44 / 5)).const_mul jet
  have hev := ((tendsto_order.mp he).2 d hd).and
    (((tendsto_order.mp hs).2 eps heps).and
      ((tendsto_order.mp hj).2 (3 * eps / 4) (by positivity)))
  obtain ⟨tau, htau, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨rho, hrho, min_le_left _ _, min tau threshold,
    lt_min htau hthreshold, min_le_right _ _, ?_⟩
  intro t ht htt s hs0 hs_rho
  have hts := hsmall ⟨ht, htt.trans_le (min_le_left _ _)⟩
  have hcs : constant * s ≤ d := by
    calc
      constant * s ≤ (constant + 1) * s := by nlinarith
      _ ≤ (constant + 1) * (d / (constant + 1)) :=
        mul_le_mul_of_nonneg_left (hs_rho.le.trans (min_le_right _ _)) (by positivity)
      _ = d := mul_div_cancel₀ d (by positivity : constant + 1 ≠ 0)
  let e := max (etaB t) (etaV t) + constant * s
  have hen : 0 ≤ e := add_nonneg ((hBn t).trans (le_max_left _ _)) (mul_nonneg hconstant hs0)
  have he2 : e ≤ 2 * d := by dsimp only [e]; linarith [hts.1]
  have hMde : M * e ≤ eps / 4 := by
    have hden : d * (8 * (M + 1)) = eps := div_mul_cancel₀ eps (by positivity)
    have hstep := mul_le_mul_of_nonneg_left he2 hM.le
    nlinarith [hden, hd]
  constructor
  · rw [mul_max_of_nonneg _ _ hamp.le]
    apply (max_le_iff).mpr
    constructor
    · calc
        amp * (4 * derivative * ((etaB t + constant * s) * frame)) =
            (4 * amp) * (derivative * frame) * (etaB t + constant * s) := by ring
        _ ≤ (4 * amp) * (derivative * frame) * e := mul_le_mul_of_nonneg_left
          (show etaB t + constant * s ≤ e from add_le_add (le_max_left _ _) le_rfl) (by positivity)
        _ ≤ M * e := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)) hen
        _ ≤ _ := hMde
    · calc
        amp * (4 * (etaV t + constant * s)) = (4 * amp) * (etaV t + constant * s) := by ring
        _ ≤ (4 * amp) * e := mul_le_mul_of_nonneg_left
          (show etaV t + constant * s ≤ e from add_le_add (le_max_right _ _) le_rfl) (by positivity)
        _ ≤ M * e := mul_le_mul_of_nonneg_right
          (by dsimp only [M]; nlinarith [le_max_right (derivative * frame) (1 : ℝ)]) hen
        _ ≤ _ := hMde
  · have hratio : |t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| = t ^ ((12 : ℝ) / 5) := by
      rw [← Real.rpow_sub ht]
      norm_num
      exact Real.rpow_nonneg ht.le _
    rw [hratio]
    exact max_le hts.2.1.le (by linarith [hts.2.2])

#print axioms rankQ_exists_probe_response_ball_scale
end GlobalEmbedding.Upgrade
