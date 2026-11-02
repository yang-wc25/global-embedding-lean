import Probes.ActualQuantitativePhaseChart
import Probes.ActualInverseChartJets

/-!
# Original phase jets control the actual coordinate differential

The derivative oscillation is proved from the original native second derivative
on the original ball. Higher forward-coordinate derivatives equal the phase
derivatives in norm: the retained parameter/transverse coordinates are linear.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology NNReal
namespace GlobalEmbedding.Continuation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_native_derivative_oscillation
    (f : E → F) (x0 : E) (R M : ℝ) (hR : 0 < R)
    (hf : ContDiffOn ℝ ∞ f (ball x0 R))
    (hsecond : ∀ x ∈ ball x0 R, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M)
    (x : E) (hx : x ∈ ball x0 R) :
    ‖fderiv ℝ f x-fderiv ℝ f x0‖ ≤ M*‖x-x0‖ := by
  have hD := hf.fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)
  apply (convex_ball x0 R).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hD.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    _ (mem_ball_self hR) hx
  intro y hy
  rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact hsecond y hy

theorem actual_linear_higher_jet_zero (L : E →L[ℝ] F) (i : ℕ) (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ (i+1) L x‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ : E => L := funext (fun y => L.fderiv)
  rw [he,iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
  simp

variable {Ep Et : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]

theorem actual_phase_coordinate_higher_jet_norm
    (psi : Ep × (ℝ × Et) → ℝ) (x : Ep × (ℝ × Et))
    (hpsi : ContDiffAt ℝ ∞ psi x) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ (i+1) (actualPhaseCoordinateMap psi) x‖ =
      ‖iteratedFDeriv ℝ (i+1) psi x‖ := by
  let Lp := ContinuousLinearMap.fst ℝ Ep (ℝ × Et)
  let Lt := (ContinuousLinearMap.snd ℝ ℝ Et).comp (ContinuousLinearMap.snd ℝ Ep (ℝ × Et))
  change ‖iteratedFDeriv ℝ (i+1) (fun z => (Lp z,(psi z,Lt z))) x‖ = _
  rw [iteratedFDeriv_prodMk Lp.contDiff.contDiffAt (hpsi.prodMk Lt.contDiff.contDiffAt) (by simp),
    ContinuousMultilinearMap.opNorm_prod,
    iteratedFDeriv_prodMk hpsi Lt.contDiff.contDiffAt (by simp),
    ContinuousMultilinearMap.opNorm_prod,
    actual_linear_higher_jet_zero Lp i hi x,actual_linear_higher_jet_zero Lt i hi x]
  simp only [max_eq_left (norm_nonneg _),max_eq_right (norm_nonneg _)]

/-- Fixed numerical inverse majorant, chosen before the phase and the scale. -/
def actualPhaseInverseConstant (mu M : ℝ) : ℝ := 1+(1+M)/mu

theorem actualPhaseInverseConstant_one_le {mu M : ℝ} (hmu : 0 < mu) (hM : 0 ≤ M) :
    1 ≤ actualPhaseInverseConstant mu M := by
  unfold actualPhaseInverseConstant
  exact le_add_of_nonneg_right (by positivity)

theorem actual_phase_inverse_constant_bound
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ)
    (haxis : mu ≤ |d (0,(1,0))|) (hD : ‖d‖ ≤ M)
    (hd : d (0,(1,0)) ≠ 0) :
    ‖((actualPhaseTriangularEquiv d hd).symm :
      (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖ ≤ actualPhaseInverseConstant mu M := by
  apply (actual_phase_triangular_inverse_bound d hd).trans
  unfold actualPhaseInverseConstant
  gcongr

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_native_derivative_oscillation
#print axioms GlobalEmbedding.Continuation.actual_phase_coordinate_higher_jet_norm
