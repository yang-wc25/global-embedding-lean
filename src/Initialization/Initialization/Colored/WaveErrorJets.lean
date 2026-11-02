import Initialization.Colored.ReferenceJets
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# All-order smallness of the actual single-wave first-derivative error

The differentiated cutoff and frozen-coframe discrepancy are actual functions.
The proof differentiates their exact product formula using the native Leibniz
estimate. In particular, the small parameter is retained in every order.
-/

noncomputable section
open Function Set Filter Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complexification of real covectors preserves their actual operator norm. -/
def complexifyCovector : (E →L[ℝ] ℝ) →ₗᵢ[ℝ] (E →L[ℝ] ℂ) :=
  Complex.ofRealLI.postcomp

@[simp] theorem complexifyCovector_apply (r : E →L[ℝ] ℝ) (v : E) :
    complexifyCovector r v = (r v : ℂ) := rfl

/-- The error uses the derivative of the literal weighted exponential. -/
def coloredWaveFirstRemainder (χ ℓ : E → ℝ) (T : ℝ)
    (r : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℂ :=
  fderiv ℝ (coloredWave χ ℓ T) x -
    (r x).smulRight ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) * coloredWave χ ℓ T x)

/-- The exact first-derivative remainder consists of a small cutoff derivative
and a small phase-rate difference, multiplied by the actual bounded waves. -/
theorem coloredWaveFirstRemainder_eq_formula (χ ℓ : E → ℝ) (T : ℝ)
    (r : E → E →L[ℝ] ℝ) (x : E)
    (hχ : DifferentiableAt ℝ χ x) (hℓ : DifferentiableAt ℝ ℓ x) :
    coloredWaveFirstRemainder χ ℓ T r x =
      (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) • complexifyCovector (fderiv ℝ χ x) +
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
        (coloredWave χ ℓ T x • complexifyCovector (T • fderiv ℝ ℓ x - r x))) := by
  ext v
  have h := coloredWave_first_error_identity χ ℓ (fderiv ℝ χ x)
    (fderiv ℝ ℓ x) (r x) T x v hχ.hasFDerivAt hℓ.hasFDerivAt
  simp only [coloredWaveFirstRemainder, sub_apply, ContinuousLinearMap.smulRight_apply,
    coloredWave, RCLike.real_smul_eq_coe_mul, add_apply, smul_apply,
    complexifyCovector_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat] at h ⊢
  generalize he : (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) = e at h ⊢
  linear_combination h

/-- A native local Leibniz estimate retains a common small factor in all jets. -/
theorem initialization_smul_jet_small {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    (O : Set E) (hO : IsOpen O) (f : E → ℂ) (g : E → G)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (x : E) (hx : x ∈ O) (j : ℕ) (A B : ℕ → ℝ) (δ : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hδ : 0 ≤ δ)
    (hfj : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f x‖ ≤ A i)
    (hgj : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ≤ B i * δ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f y • g y) x‖ ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * B (j-i)) * δ := by
  have h := norm_iteratedFDerivWithin_smul_le hf hg hO.uniqueDiffOn hx
    (by simp : (j : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at h
  refine h.trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  calc
    _ ≤ (j.choose i : ℝ) * A i * (B (j-i) * δ) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj i hij) (by positivity))
        (hgj (j-i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (by positivity) (hA i))
    _ = _ := by ring

/-- The exact C^j coefficient in the single-wave remainder estimate. -/
def coloredWaveErrorBound (A L : ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * coloredPhaseReferenceBound L i * A) +
  (2 * Real.pi) *
    (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * coloredWaveReferenceBound A L i * A)

theorem coloredWaveErrorBound_nonneg (A L : ℝ) (hA : 0 ≤ A) (j : ℕ) :
    0 ≤ coloredWaveErrorBound A L j := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (by positivity)
      (by unfold coloredPhaseReferenceBound; positivity)) hA
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (by positivity)
      (coloredWaveReferenceBound_nonneg A L hA i)) hA

/-- All actual derivatives of the same first-derivative remainder retain δ.
The small cutoff budget is placed on its positive-order derivatives; the phase
discrepancy is the genuine field T*d ell-r, rather than an independent jet. -/
theorem coloredWaveFirstRemainder_jet_bound
    (O : Set E) (hO : IsOpen O) (χ ℓ : E → ℝ) (r : E → E →L[ℝ] ℝ)
    (hχ : ContDiffOn ℝ ∞ χ O) (hℓ : ContDiffOn ℝ ∞ ℓ O)
    (hr : ContDiffOn ℝ ∞ r O) (T A L δ : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (x : E) (hx : x ∈ O) (j : ℕ)
    (hcutoff : ∀ i ≤ j, ‖iteratedFDeriv ℝ i χ x‖ ≤ A)
    (hcutoffSmall : ∀ i ≤ j, ‖iteratedFDeriv ℝ (i+1) χ x‖ ≤ A * δ)
    (hphase : ∀ i, 1 ≤ i → i ≤ j → |T| * ‖iteratedFDeriv ℝ i ℓ x‖ ≤ L)
    (hrate : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i (fun y ↦ T • fderiv ℝ ℓ y - r y) x‖ ≤ A * δ) :
    ‖iteratedFDeriv ℝ j (coloredWaveFirstRemainder χ ℓ T r) x‖ ≤
      coloredWaveErrorBound A L j * δ := by
  let e : E → ℂ := fun y ↦ (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ)
  let a : E → E →L[ℝ] ℂ := fun y ↦ complexifyCovector (fderiv ℝ χ y)
  let b : E → E →L[ℝ] ℂ := fun y ↦ complexifyCovector (T • fderiv ℝ ℓ y - r y)
  let W := coloredWave χ ℓ T
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  let U : E → E →L[ℝ] ℂ := fun y ↦ e y • a y
  let V : E → E →L[ℝ] ℂ := fun y ↦ W y • b y
  have he : ContDiffOn ℝ ∞ e O := (coloredExponential_contDiff T).comp_contDiffOn hℓ
  have hdχ := hχ.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  have hdℓ := hℓ.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  have hdr : ContDiffOn ℝ ∞ (fun y ↦ T • fderiv ℝ ℓ y - r y) O :=
    (hdℓ.const_smul T).sub hr
  have ha : ContDiffOn ℝ ∞ a O :=
    complexifyCovector.toContinuousLinearMap.contDiff.comp_contDiffOn hdχ
  have hb : ContDiffOn ℝ ∞ b O :=
    complexifyCovector.toContinuousLinearMap.contDiff.comp_contDiffOn
      hdr
  have hW : ContDiffOn ℝ ∞ W O := hχ.smul he
  have hU : ContDiffOn ℝ ∞ U O := he.smul ha
  have hV : ContDiffOn ℝ ∞ V O := hW.smul hb
  have haSmall (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i a x‖ ≤ A * δ := by
    rw [show a = complexifyCovector ∘ fderiv ℝ χ from rfl,
      complexifyCovector.norm_iteratedFDeriv_comp_left
        (hdχ.contDiffAt (hO.mem_nhds hx)) (by simp : (i : ℕ∞ω) ≤ ∞),
      norm_iteratedFDeriv_fderiv]
    exact hcutoffSmall i hi
  have hbSmall (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i b x‖ ≤ A * δ := by
    rw [show b = complexifyCovector ∘ (fun y ↦ T • fderiv ℝ ℓ y - r y) from rfl,
      complexifyCovector.norm_iteratedFDeriv_comp_left
        (hdr.contDiffAt (hO.mem_nhds hx))
        (by simp : (i : ℕ∞ω) ≤ ∞)]
    exact hrate i hi
  have hUb := initialization_smul_jet_small O hO e a he ha x hx j
    (coloredPhaseReferenceBound L) (fun _ ↦ A) δ
    (fun _ ↦ by unfold coloredPhaseReferenceBound; positivity) (fun _ ↦ hA) hδ
    (coloredExponential_reference_bound O hO ℓ hℓ T L x hx j hphase) haSmall
  have hVb := initialization_smul_jet_small O hO W b hW hb x hx j
    (coloredWaveReferenceBound A L) (fun _ ↦ A) δ
    (coloredWaveReferenceBound_nonneg A L hA) (fun _ ↦ hA) hδ ?_ hbSmall
  · have hEq : coloredWaveFirstRemainder χ ℓ T r =ᶠ[𝓝 x] fun y ↦ U y + c • V y := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact coloredWaveFirstRemainder_eq_formula χ ℓ T r y
        ((hχ.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
        ((hℓ.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
    rw [(hEq.iteratedFDeriv ℝ j).self_of_nhds]
    rw [show (fun y ↦ U y + c • V y) = U + (fun y ↦ c • V y) from rfl,
      iteratedFDeriv_add_apply
        ((hU.contDiffAt (hO.mem_nhds hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
        (((hV.const_smul c).contDiffAt (hO.mem_nhds hx)).of_le
          (by simp : (j : ℕ∞ω) ≤ ∞))]
    have hc : ‖c‖ = 2 * Real.pi := by
      simp [c, norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
    have hcb := (c • ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ)).norm_iteratedFDeriv_comp_left
      (hV.contDiffAt (hO.mem_nhds hx)) (by simp : (j : ℕ∞ω) ≤ ∞)
    have hcb' : ‖iteratedFDeriv ℝ j (fun y ↦ c • V y) x‖ ≤
        ‖c‖ * ‖iteratedFDeriv ℝ j V x‖ := by
      have hl : ‖c • ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ)‖ ≤ ‖c‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
        intro u
        simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul]
        rfl
      exact hcb.trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))
    calc
      _ ≤ ‖iteratedFDeriv ℝ j U x‖ + ‖iteratedFDeriv ℝ j (fun y ↦ c • V y) x‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * coloredPhaseReferenceBound L i * A) * δ +
          (2 * Real.pi) *
            ((∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * coloredWaveReferenceBound A L i * A) * δ) :=
        add_le_add hUb (by
          rw [hc] at hcb'
          exact hcb'.trans (mul_le_mul_of_nonneg_left hVb (by positivity)))
      _ = coloredWaveErrorBound A L j * δ := by unfold coloredWaveErrorBound; ring
  · intro i hi
    exact coloredWave_reference_bound O hO χ ℓ hχ hℓ T A L hA x hx i
      (fun k hk ↦ hcutoff k (hk.trans hi))
      (fun k hk hki ↦ hphase k hk (hki.trans hi))

end GlobalEmbedding.Initialization
