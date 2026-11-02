import NormalPolar.FullResponseScales
import GlobalEmbedding.Paper.ProjectedHessianChain

/-!
# Native probe responses under the actual source-coordinate transition

The complete prescribed wave is constructed in its own phase chart. The
original probe record observes its native Hessian in every original atlas
chart. The change of chart contributes both Jacobian factors and the second
derivative of the transition. The latter multiplies the genuine first
derivative of the parameter response; it is not discarded as a normal term.
-/

noncomputable section
open Filter Set Function GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

section HessianChain
variable {X Z Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The unprojected chain rule retains the coordinate-acceleration term. -/
theorem globalWave_native_hessian_chain_apply
    (f : X → Y) (φ : Z → X) (x : Z)
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (v w : Z) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) x v w =
      fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) +
        fderiv ℝ f (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (φ x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ0 : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have heq : (fun y ↦ fderiv ℝ (f ∘ φ) y) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y)) := by
    filter_upwards [hφ.eventually (by norm_num),
      hφ.continuousAt.eventually (hf.eventually (by norm_num))] with y hyφ hyf
    exact fderiv_comp y (hyf.differentiableAt (by norm_num))
      (hyφ.differentiableAt (by norm_num))
  rw [heq.fderiv_eq,
    fderiv_clm_comp (c := fun y ↦ fderiv ℝ f (φ y)) (hf'.comp x hφ0) hφ',
    fderiv_fun_comp x hf' hφ0]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  exact add_comm _ _

/-- The fast phase tensor is genuinely covariant under the same transition. -/
theorem globalWave_phase_hessian_pullback
    (θ : X → ℝ) (amplitude : X → Y) (φ : Z → X) (x : Z)
    (hθ : DifferentiableAt ℝ θ (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    phaseRankOneHessian (θ ∘ φ) (amplitude ∘ φ) x =
      (phaseRankOneHessian θ amplitude (φ x)).bilinearComp
        (fderiv ℝ φ x) (fderiv ℝ φ x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [phaseRankOneHessian, fderiv_comp x hθ hφ,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.bilinearComp_apply, Function.comp_apply, smul_apply]

/-- Native Hessian error in an arbitrary observer chart. The second
transition jet is charged to the actual response first jet. -/
theorem globalWave_native_hessian_error_change_coordinates
    (f : X → Y) (θ : X → ℝ) (amplitude : X → Y) (φ : Z → X)
    (x : Z) (coefficient error : ℝ)
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hθ : DifferentiableAt ℝ θ (φ x))
    (herror : 0 ≤ error)
    (hbound : ‖fderiv ℝ (fderiv ℝ f) (φ x) -
      coefficient • phaseRankOneHessian θ amplitude (φ x)‖ ≤ error) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ φ)) x -
      coefficient • phaseRankOneHessian (θ ∘ φ) (amplitude ∘ φ) x‖ ≤
      error * ‖fderiv ℝ φ x‖ ^ 2 +
        ‖fderiv ℝ f (φ x)‖ * ‖fderiv ℝ (fderiv ℝ φ) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  have hident :
      (fderiv ℝ (fderiv ℝ (f ∘ φ)) x -
        coefficient • phaseRankOneHessian (θ ∘ φ) (amplitude ∘ φ) x) v w =
      (fderiv ℝ (fderiv ℝ f) (φ x) -
        coefficient • phaseRankOneHessian θ amplitude (φ x))
          (fderiv ℝ φ x v) (fderiv ℝ φ x w) +
        fderiv ℝ f (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) := by
    rw [sub_apply, sub_apply,
      globalWave_native_hessian_chain_apply f φ x hf hφ v w,
      globalWave_phase_hessian_pullback θ amplitude φ x hθ
        (hφ.differentiableAt (by norm_num))]
    simp only [smul_apply, ContinuousLinearMap.bilinearComp_apply,
      sub_apply]
    abel
  rw [hident]
  calc
    _ ≤ ‖(fderiv ℝ (fderiv ℝ f) (φ x) -
          coefficient • phaseRankOneHessian θ amplitude (φ x))
            (fderiv ℝ φ x v) (fderiv ℝ φ x w)‖ +
        ‖fderiv ℝ f (φ x) (fderiv ℝ (fderiv ℝ φ) x v w)‖ := norm_add_le _ _
    _ ≤ error * (‖fderiv ℝ φ x‖ * ‖v‖) * (‖fderiv ℝ φ x‖ * ‖w‖) +
        ‖fderiv ℝ f (φ x)‖ * (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖v‖ * ‖w‖) := by
      apply add_le_add
      · exact ((fderiv ℝ (fderiv ℝ f) (φ x) -
          coefficient • phaseRankOneHessian θ amplitude (φ x)).le_opNorm₂ _ _).trans
          (by gcongr; exacts [(fderiv ℝ φ x).le_opNorm v,
            (fderiv ℝ φ x).le_opNorm w])
      · exact ((fderiv ℝ f (φ x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm₂ v w)
            (norm_nonneg _))
    _ = _ := by ring

end HessianChain

section ParameterResponse
variable {P X Z Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Apply the coordinate-change estimate to the same literal parameter
derivative of a jointly smooth mapping family. No new response field is
chosen, and the original parameter domain is kept. -/
theorem globalWave_actual_parameter_hessian_error_change_coordinates
    {U : Set P} {S : Set X} {O : Set Z}
    (hU : IsOpen U) (hS : IsOpen S) (hO : IsOpen O)
    (F : P → X → Y) (φ : Z → X)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (U ×ˢ S))
    (hφ : ContDiffOn ℝ ∞ φ O) (hmap : MapsTo φ O S)
    (θ : X → ℝ) (amplitude : X → Y)
    (u d : P) (hu : u ∈ U) (x : Z) (hx : x ∈ O)
    (coefficient error : ℝ) (herror : 0 ≤ error)
    (hθ : DifferentiableAt ℝ θ (φ x))
    (hbound : ‖fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v)) (φ x)) u d -
      coefficient • phaseRankOneHessian θ amplitude (φ x)‖ ≤ error) :
    ‖fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ φ)) x) u d -
      coefficient • phaseRankOneHessian (θ ∘ φ) (amplitude ∘ φ) x‖ ≤
      error * ‖fderiv ℝ φ x‖ ^ 2 +
        ‖fderiv ℝ (fun y ↦ fderiv ℝ (fun v ↦ F v y) u d) (φ x)‖ *
          ‖fderiv ℝ (fderiv ℝ φ) x‖ := by
  let R : X → Y := fun y ↦ fderiv ℝ (fun v ↦ F v y) u d
  have hD := (contDiffOn_actual_parameter_fderiv (hU.prod hS) hF).clm_apply
    (contDiffOn_const (c := d))
  have hR : ContDiffOn ℝ ∞ R S :=
    hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy ↦ ⟨hu, hy⟩)
  have hFc : ContDiffOn ℝ ∞ (fun z : P × Z ↦ F z.1 (φ z.2)) (U ×ˢ O) := by
    exact hF.comp (contDiffOn_fst.prodMk (hφ.comp contDiffOn_snd (fun _ hz ↦ hz.2)))
      (fun z hz ↦ ⟨hz.1, hmap hz.2⟩)
  have hcomm := actual_parameter_spatial_second_fderiv_comm (hU.prod hS)
    (Function.uncurry F) hF u (φ x) d ⟨hu, hmap hx⟩
  have hcommc := actual_parameter_spatial_second_fderiv_comm (hU.prod hO)
    (fun z : P × Z ↦ F z.1 (φ z.2)) hFc u x d ⟨hu, hx⟩
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm] at hbound
  change ‖fderiv ℝ (fderiv ℝ R) (φ x) -
    coefficient • phaseRankOneHessian θ amplitude (φ x)‖ ≤ error at hbound
  rw [show (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ φ)) x) =
      (fun v ↦ fderiv ℝ (fderiv ℝ (fun s ↦ F v (φ s))) x) from rfl, hcommc]
  exact globalWave_native_hessian_error_change_coordinates R θ amplitude φ x coefficient error
    ((hR.contDiffAt (hS.mem_nhds (hmap hx))).of_le (by simp))
    ((hφ.contDiffAt (hO.mem_nhds hx)).of_le (by simp)) hθ herror hbound

end ParameterResponse
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.globalWave_native_hessian_error_change_coordinates
#print axioms GlobalEmbedding.NormalPolar.globalWave_actual_parameter_hessian_error_change_coordinates
