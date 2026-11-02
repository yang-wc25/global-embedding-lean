import NormalPolar.GlobalWaveResponseBackgroundActualResponse
import NormalPolar.GlobalWaveResponseBackgroundActualC1
import NormalPolar.OriginalProbeScales

/-! Physical scaling and the literal original paired parameters for the full
background response. The exact linear isometry preserves the original ball.
The value, first-spatial-jet and Hessian scales are respectively delta*tau,
delta and delta/tau. All derivatives are derivatives of the same scaled map. -/
noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private local instance bgPhysicalHessianSemi : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance bgPhysicalHessianNormed : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance bgPhysicalHessianSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace

/-- Constant real physical scaling commutes with the actual totalized first
derivative, including the zero scalar. -/
theorem globalWave_native_first_smul (f : X → Y) (delta : ℝ) (x : X) :
    fderiv ℝ (fun y => delta • f y) x = delta • fderiv ℝ f x := by
  exact congrFun (fderiv_const_smul_field (𝕜:=ℝ) (f:=f) delta) x

/-- The same exact identity at spatial order two. -/
theorem globalWave_native_hessian_smul (f : X → Y) (delta : ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ (fun y => delta • f y)) x =
      delta • fderiv ℝ (fderiv ℝ f) x := by
  change fderiv ℝ (fderiv ℝ (delta • f)) x = _
  rw [fderiv_const_smul_field]
  exact congrFun (fderiv_const_smul_field (𝕜:=ℝ) (f:=fderiv ℝ f) delta) x

theorem globalWave_paired_scaled_native_bound {r p : ℕ}
    (label : (Fin r × Bool) ↪ Fin p) (f : (Fin p → ℝ) → Y)
    (u : ProbeParameters r) (delta B : ℝ)
    (hD : HasFDerivAt f (fderiv ℝ f (probeParameterEmbedding label u))
      (probeParameterEmbedding label u))
    (hb : ‖fderiv ℝ f (probeParameterEmbedding label u)‖ ≤ B*‖probeParameterEmbedding label u‖) :
    HasFDerivAt (fun v => delta • f (probeParameterEmbedding label v))
      (fderiv ℝ (fun v => delta • f (probeParameterEmbedding label v)) u) u ∧
    ‖fderiv ℝ (fun v => delta • f (probeParameterEmbedding label v)) u‖ ≤ |delta| *B*‖u‖ := by
  have h := (hD.comp u (probeParameterEmbedding label).toContinuousLinearMap.hasFDerivAt).const_smul delta
  have hc : ‖(fderiv ℝ f (probeParameterEmbedding label u)).comp
      (probeParameterEmbedding label).toContinuousLinearMap‖ ≤
      ‖fderiv ℝ f (probeParameterEmbedding label u)‖ := by
    apply ((fderiv ℝ f (probeParameterEmbedding label u)).comp
      (probeParameterEmbedding label).toContinuousLinearMap).opNorm_le_bound (norm_nonneg _)
    intro d
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      probeParameterEmbedding_norm] using
      (fderiv ℝ f (probeParameterEmbedding label u)).le_opNorm (probeParameterEmbedding label d)
  refine ⟨h.differentiableAt.hasFDerivAt,?_⟩
  change ‖fderiv ℝ (delta • (f ∘ probeParameterEmbedding label)) u‖ ≤ _
  rw [h.fderiv,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |delta| *‖fderiv ℝ f (probeParameterEmbedding label u)‖ :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg delta)
    _ ≤ |delta| *(B*‖probeParameterEmbedding label u‖) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg delta)
    _ = _ := by rw [probeParameterEmbedding_norm]; ring

/-- Consume the three actual unscaled background responses, without
changing their parameter domain, map, or derivatives. -/
theorem globalWave_background_native_paired_paper_scales {r p : ℕ}
    (label : (Fin r × Bool) ↪ Fin p) (f : (Fin p → ℝ) → X → Y)
    (u : ProbeParameters r) (x : X) (t C : ℝ) (ht : 0 < t)
    (hV : HasFDerivAt (fun v => f v x)
      (fderiv ℝ (fun v => f v x) (probeParameterEmbedding label u)) (probeParameterEmbedding label u) ∧
      ‖fderiv ℝ (fun v => f v x) (probeParameterEmbedding label u)‖ ≤
        (C*t ^ ((6:ℝ)/5))*‖probeParameterEmbedding label u‖)
    (hD : HasFDerivAt (fun v => fderiv ℝ (f v) x)
      (fderiv ℝ (fun v => fderiv ℝ (f v) x) (probeParameterEmbedding label u)) (probeParameterEmbedding label u) ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (f v) x) (probeParameterEmbedding label u)‖ ≤
        C*‖probeParameterEmbedding label u‖)
    (hH : HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) x)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) x) (probeParameterEmbedding label u))
        (probeParameterEmbedding label u) ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) x) (probeParameterEmbedding label u)‖ ≤
        (C/t ^ ((6:ℝ)/5))*‖probeParameterEmbedding label u‖) :
    let B := fun v y => t^(10:ℕ) • f (probeParameterEmbedding label v) y
    (HasFDerivAt (fun v => B v x) (fderiv ℝ (fun v => B v x) u) u ∧
      ‖fderiv ℝ (fun v => B v x) u‖ ≤ (C*t ^ ((56:ℝ)/5))*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (B v) x)
      (fderiv ℝ (fun v => fderiv ℝ (B v) x) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (B v) x) u‖ ≤ (C*t^(10:ℕ))*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (B v)) x)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (B v)) x) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (B v)) x) u‖ ≤ (C*t ^ ((44:ℝ)/5))*‖u‖) := by
  intro B
  have hv := globalWave_paired_scaled_native_bound label (fun v => f v x) u
    (t^(10:ℕ)) (C*t ^ ((6:ℝ)/5)) hV.1 hV.2
  have hd := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (f v) x) u
    (t^(10:ℕ)) C hD.1 hD.2
  have hh := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (fderiv ℝ (f v)) x) u
    (t^(10:ℕ)) (C/t ^ ((6:ℝ)/5)) hH.1 hH.2
  have hvscale : |t^(10:ℕ)| *(C*t ^ ((6:ℝ)/5)) = C*t ^ ((56:ℝ)/5) := by
    rw [abs_of_pos (pow_pos ht 10),← probe_delta_mul_tau_eq_value_scale t ht]
    ring
  have hdscale : |t^(10:ℕ)| *C = C*t^(10:ℕ) := by rw [abs_of_pos (pow_pos ht 10),mul_comm]
  have hhscale : |t^(10:ℕ)| *(C/t ^ ((6:ℝ)/5)) = C*t ^ ((44:ℝ)/5) := by
    rw [abs_of_pos (pow_pos ht 10),← probe_delta_div_tau_eq_sigma t ht]
    ring
  rw [hvscale] at hv
  rw [hdscale] at hd
  rw [hhscale] at hh
  refine ⟨hv,?_,?_⟩
  · have he : (fun v => fderiv ℝ (B v) x) =
        (fun v => t^(10:ℕ) • fderiv ℝ (f (probeParameterEmbedding label v)) x) := by
      funext v
      exact globalWave_native_first_smul _ _ _
    rw [he]
    exact hd
  · have he : (fun v => fderiv ℝ (fderiv ℝ (B v)) x) =
        (fun v => t^(10:ℕ) • fderiv ℝ (fderiv ℝ (f (probeParameterEmbedding label v))) x) := by
      funext v
      exact globalWave_native_hessian_smul _ _ _
    rw [he]
    exact hh

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_native_paired_paper_scales
