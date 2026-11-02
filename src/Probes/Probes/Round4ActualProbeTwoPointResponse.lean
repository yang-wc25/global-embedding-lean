import Probes.Round4ActualProbeReserveDifference
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Linear parameter response from an actual quadratic two-point estimate

This is the analytic last step after the original whole-field tame difference
estimate. It does not equip the tensor germ space with a fictitious Banach norm.
It applies to each actual normed output of that field, such as a chart jet at a
point. The `HasFDerivAt` version explicitly retains genuine differentiability;
the totalized `fderiv` bound alone makes no regularity assertion.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace GlobalEmbedding.Continuation

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A quadratic two-point estimate has the sharp first-response constant 2C. -/
theorem round4_hasFDerivAt_le_of_quadratic_difference
    (f : P → Y) (U : Set P) (u : P) (hU : U ∈ 𝓝 u) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ v ∈ U, ‖f v-f u‖ ≤ C*(‖v‖+‖u‖)*‖v-u‖)
    (D : P →L[ℝ] Y) (hD : HasFDerivAt f D u) : ‖D‖ ≤ 2*C*‖u‖ := by
  refine le_of_forall_pos_le_add fun e he => ?_
  let eta := e/(C+1)
  have hCp : 0 < C+1 := by linarith
  have heta : 0 < eta := div_pos he hCp
  have hsmall : C*eta ≤ e := by
    have hh : C ≤ C+1 := by linarith
    calc
      C*eta ≤ (C+1)*eta := mul_le_mul_of_nonneg_right hh heta.le
      _ = e := by dsimp only [eta]; field_simp
  have hnear : ∀ᶠ v in 𝓝 u, ‖v‖ < ‖u‖+eta :=
    continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith))
  apply hD.le_of_lip' (show 0 ≤ 2*C*‖u‖+e by positivity)
  filter_upwards [hU,hnear] with v hv hn
  calc
    ‖f v-f u‖ ≤ C*(‖v‖+‖u‖)*‖v-u‖ := hpair v hv
    _ ≤ (2*C*‖u‖+e)*‖v-u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        C*(‖v‖+‖u‖) ≤ C*((‖u‖+eta)+‖u‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hn.le le_rfl) hC
        _ ≤ 2*C*‖u‖+e := by nlinarith

/-- The same norm bound for Lean's totalized derivative. This theorem does not
assert that the function is differentiable. -/
theorem round4_fderiv_le_of_quadratic_difference
    (f : P → Y) (U : Set P) (u : P) (hU : U ∈ 𝓝 u) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ v ∈ U, ‖f v-f u‖ ≤ C*(‖v‖+‖u‖)*‖v-u‖) :
    ‖fderiv ℝ f u‖ ≤ 2*C*‖u‖ := by
  by_cases hd : DifferentiableAt ℝ f u
  · exact round4_hasFDerivAt_le_of_quadratic_difference f U u hU C hC hpair
      (fderiv ℝ f u) hd.hasFDerivAt
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simpa using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hC) (norm_nonneg u)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_hasFDerivAt_le_of_quadratic_difference
#print axioms GlobalEmbedding.Continuation.round4_fderiv_le_of_quadratic_difference
