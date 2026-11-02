import Initialization.Colored.FirstDerivative
import Initialization.Colored.LocalGerms
import GlobalEmbedding.Paper.IncrementsFastPhaseJet
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Fixed-order reference bounds for the actual colored phases

Constants are chosen from the rescaled cutoff and phase-rate budgets before
frequency and chart count. The only use of the increments branch is its already
published exact real-jet norm of the scalar complex exponential; no increments
or repair source is modified or re-proved here.
-/

noncomputable section

open Function Set Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed outer-composition budget. It is independent of K and T. -/
def coloredPhaseReferenceBound (L : ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * (max 1 (2 * Real.pi * L)) ^ j

/-- The exact linear phase insertion has norm 2π|T|. -/
theorem coloredPhaseLinear_norm (T : ℝ) :
    ‖coloredPhaseLinear T‖ = 2 * Real.pi * |T| := by
  simp [coloredPhaseLinear, norm_smul, Complex.ofRealCLM_norm,
    Complex.norm_real, abs_of_pos Real.pi_pos]

/-- Every actual rescaled phase jet has a frequency-independent bound, supplied
by genuine derivative budgets |T|*|D^i ell|≤L. No bound on the phase value itself
is needed. The hypotheses concern only the derivatives of the actual phase. -/
theorem coloredExponential_reference_bound
    (O : Set E) (hO : IsOpen O) (ℓ : E → ℝ) (hℓ : ContDiffOn ℝ ∞ ℓ O)
    (T L : ℝ) (x : E) (hx : x ∈ O) (j : ℕ)
    (hjet : ∀ i, 1 ≤ i → i ≤ j →
      |T| * ‖iteratedFDeriv ℝ i ℓ x‖ ≤ L) :
    ∀ a ≤ j, ‖iteratedFDeriv ℝ a
      (fun y ↦ (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ)) x‖ ≤
        coloredPhaseReferenceBound L a := by
  let P := coloredPhaseLinear T
  let φ : E → ℂ := P ∘ ℓ
  let R := max 1 (2 * Real.pi * L)
  have hR : 1 ≤ R := le_max_left _ _
  have hφ : ContDiffOn ℝ ∞ φ O := P.contDiff.comp_contDiffOn hℓ
  have hφeq (y : E) : φ y = Complex.I * ((2 * Real.pi * T * ℓ y : ℝ) : ℂ) := by
    simp only [φ, P, Function.comp_apply, coloredPhaseLinear, smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  intro a ha
  have hout (i : ℕ) (_hi : i ≤ a) :
      ‖iteratedFDerivWithin ℝ i Complex.exp univ (φ x)‖ ≤ (1 : ℝ) := by
    rw [iteratedFDerivWithin_univ, hφeq,
      GlobalEmbedding.Paper.increments_phase_exp_real_jet_norm]
  have hin (i : ℕ) (hi : 1 ≤ i) (hia : i ≤ a) :
      ‖iteratedFDerivWithin ℝ i φ O x‖ ≤ R ^ i := by
    have hlin := P.norm_iteratedFDerivWithin_comp_left
      (hℓ x hx) hO.uniqueDiffOn hx (by simp : (i : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ‖P‖ * ‖iteratedFDerivWithin ℝ i ℓ O x‖ := hlin
      _ = (2 * Real.pi) * (|T| * ‖iteratedFDeriv ℝ i ℓ x‖) := by
        rw [iteratedFDerivWithin_of_isOpen i hO hx]
        dsimp only [P]
        rw [coloredPhaseLinear_norm]
        ring
      _ ≤ 2 * Real.pi * L := mul_le_mul_of_nonneg_left (hjet i hi (hia.trans ha))
        (by positivity)
      _ ≤ R := le_max_right _ _
      _ ≤ R ^ i := le_self_pow₀ hR (by omega)
  have hc := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℝ) (n := a) (s := O) (t := univ)
    (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).contDiffOn hφ
    (by simp : (a : ℕ∞ω) ≤ ∞) uniqueDiffOn_univ hO.uniqueDiffOn
    (by intro y hy; trivial) hx hout hin
  have heq : Complex.exp ∘ φ =
      fun y ↦ (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ) := by
    funext y
    change Complex.exp (φ y) = Complex.exp _
    rw [hφeq]
    congr 1
    ring
  rw [iteratedFDerivWithin_of_isOpen a hO hx, heq, mul_one] at hc
  exact hc

/-- A fixed binomial budget for the weighted local terms of (7.2). -/
def coloredWaveReferenceBound (A L : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A *
    coloredPhaseReferenceBound L (j - i)

theorem coloredWaveReferenceBound_nonneg (A L : ℝ) (hA : 0 ≤ A) (j : ℕ) :
    0 ≤ coloredWaveReferenceBound A L j := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (by positivity) hA)
    (by unfold coloredPhaseReferenceBound; positivity)

/-- The actual local wave has fixed-order reference bounds by the native
Leibniz rule. Phase values, frequency and total patch count are absent from the
chosen right-hand constant. -/
theorem coloredWave_reference_bound
    (O : Set E) (hO : IsOpen O) (χ ℓ : E → ℝ)
    (hχ : ContDiffOn ℝ ∞ χ O) (hℓ : ContDiffOn ℝ ∞ ℓ O)
    (T A L : ℝ) (hA : 0 ≤ A) (x : E) (hx : x ∈ O) (j : ℕ)
    (hcutoff : ∀ i ≤ j, ‖iteratedFDeriv ℝ i χ x‖ ≤ A)
    (hphase : ∀ i, 1 ≤ i → i ≤ j →
      |T| * ‖iteratedFDeriv ℝ i ℓ x‖ ≤ L) :
    ‖iteratedFDeriv ℝ j (coloredWave χ ℓ T) x‖ ≤ coloredWaveReferenceBound A L j := by
  have he : ContDiffOn ℝ ∞
      (fun y ↦ (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ)) O :=
    (coloredExponential_contDiff T).comp_contDiffOn hℓ
  have hb := norm_iteratedFDerivWithin_smul_le hχ he hO.uniqueDiffOn hx
    (by simp : (j : ℕ∞ω) ≤ ∞)
  have hfull (k : ℕ) (f : E → ℂ) :
      iteratedFDerivWithin ℝ k f O x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_of_isOpen k hO hx
  have hfullR (k : ℕ) (f : E → ℝ) :
      iteratedFDerivWithin ℝ k f O x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_of_isOpen k hO hx
  simp only [hfull, hfullR] at hb
  refine hb.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hc := hcutoff i hij
  have hp := coloredExponential_reference_bound O hO ℓ hℓ T L x hx j hphase (j-i)
    (Nat.sub_le _ _)
  gcongr

end GlobalEmbedding.Initialization
