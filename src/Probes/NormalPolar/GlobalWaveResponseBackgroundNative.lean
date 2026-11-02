import Probes.Round4ActualProbeTwoPointResponse
import Probes.ActualSecondaryMixedJets

/-! Native value and spatial-Hessian parameter responses from the actual
fast two-point jets. Both maps are proved differentiable on the true joint
domain; no estimate on a totalized nonsmooth derivative is used. -/
noncomputable section
open Set Function Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

variable {P Ep Es Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private local instance bgHessianSemi : SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance bgHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance bgHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace

/-- Native Hessians subtract on genuine C2 germs. -/
theorem globalWave_native_hessian_sub
    (f g : Es → Y) (x : Es) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y-g y)) x =
      fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y-g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y-fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    exact fderiv_fun_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_sub
    ((hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))

theorem globalWave_native_background_value_hessian_of_fast_difference
    (f : P → Ep×Es → Y) (U : Set P) (O : Set (Ep×Es))
    (hU : IsOpen U) (hO : IsOpen O)
    (hjoint : ContDiffOn ℝ ∞ (fun z : (P×Ep)×Es => f z.1.1 (z.1.2,z.2))
      {z | z.1.1 ∈ U ∧ (z.1.2,z.2) ∈ O})
    (u : P) (hu : u ∈ U) (y : Ep×Es) (hy : y ∈ O)
    (tau C : ℝ) (htau : 0 < tau) (hC : 0 ≤ C)
    (hpair : ∀ v ∈ U, ∀ k ≤ 2,
      tau^k*‖iteratedFDeriv ℝ k (fun x => f v x-f u x) y‖ ≤
        C*tau*(‖v‖+‖u‖)*‖v-u‖) :
    (HasFDerivAt (fun v => f v y) (fderiv ℝ (fun v => f v y) u) u ∧
      ‖fderiv ℝ (fun v => f v y) u‖ ≤ 2*(C*tau)*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (fun x => f v (y.1,x))) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (fun x => f v (y.1,x))) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (fun x => f v (y.1,x))) y.2) u‖ ≤
        2*(C/tau)*‖u‖) := by
  let Ω : Set ((P×Ep)×Es) := {z | z.1.1 ∈ U ∧ (z.1.2,z.2) ∈ O}
  have hΩ : IsOpen Ω := (hU.preimage continuous_fst.fst).inter
    (hO.preimage (continuous_fst.snd.prodMk continuous_snd))
  have hyΩ : ((u,y.1),y.2) ∈ Ω := ⟨hu,hy⟩
  have hfs (v : P) (hv : v ∈ U) : ContDiffOn ℝ ∞ (f v) O := by
    exact hjoint.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun x hx => ⟨hv,hx⟩)
  have hvalue : ContDiffAt ℝ ∞ (fun v => f v y) u :=
    (hjoint.contDiffAt (hΩ.mem_nhds hyΩ)).comp u
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)
  have hDv := (hvalue.differentiableAt (by simp)).hasFDerivAt
  have hV : ‖fderiv ℝ (fun v => f v y) u‖ ≤ 2*(C*tau)*‖u‖ := by
    apply round4_hasFDerivAt_le_of_quadratic_difference (fun v => f v y) U u
      (hU.mem_nhds hu) (C*tau) (by positivity) _ _ hDv
    intro v hv
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hpair v hv 0 (by omega)
  have hjet := (incrementsJointSpatialJets_bridge
    (fun z : (P×Ep)×Es => f z.1.1 (z.1.2,z.2)) Ω hΩ hjoint).2.2
  have hH : ContDiffAt ℝ ∞
      (fun v => fderiv ℝ (fderiv ℝ (fun x => f v (y.1,x))) y.2) u :=
    (hjet.contDiffAt (hΩ.mem_nhds hyΩ)).comp u
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)
  have hDH := (hH.differentiableAt (by simp)).hasFDerivAt
  refine ⟨⟨hDv,hV⟩,hDH,?_⟩
  apply round4_hasFDerivAt_le_of_quadratic_difference _ U u (hU.mem_nhds hu)
    (C/tau) (by positivity) _ _ hDH
  intro v hv
  have hdiff : ContDiffOn ℝ ∞ (fun x => f v x-f u x) O := (hfs v hv).sub (hfs u hu)
  have hb := spatial_second_jet_le hO hdiff hy 0
  simp only [norm_iteratedFDeriv_zero,Nat.zero_add] at hb
  have hs (w : P) (hw : w ∈ U) : ContDiffAt ℝ 2 (fun x => f w (y.1,x)) y.2 :=
    (((hfs w hw).contDiffAt (hO.mem_nhds hy)).comp y.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  rw [globalWave_native_hessian_sub _ _ _ (hs v hv) (hs u hu)] at hb
  have hj := (mul_le_mul_of_nonneg_left hb (sq_nonneg tau)).trans (hpair v hv 2 (by omega))
  rw [mul_comm (tau^2)] at hj
  apply (le_div_iff₀ (sq_pos_of_pos htau)).2 at hj
  have he : C*tau*(‖v‖+‖u‖)*‖v-u‖/tau^2 = (C/tau)*(‖v‖+‖u‖)*‖v-u‖ := by
    field_simp [htau.ne']
  exact hj.trans_eq he

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_background_value_hessian_of_fast_difference
