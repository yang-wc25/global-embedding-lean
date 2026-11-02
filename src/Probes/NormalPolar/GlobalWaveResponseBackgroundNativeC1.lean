import NormalPolar.GlobalWaveResponseBackgroundNative

/-! The sharp first spatial parameter response of the same full background.
The factor tau in the genuine two-point fast jet cancels the one first
derivative weight. This is not inferred by interpolation from values and
Hessians. -/
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

theorem globalWave_native_background_first_of_fast_difference
    (f : P → Ep×Es → Y) (U : Set P) (O : Set (Ep×Es))
    (hU : IsOpen U) (hO : IsOpen O)
    (hjoint : ContDiffOn ℝ ∞ (fun z : (P×Ep)×Es => f z.1.1 (z.1.2,z.2))
      {z | z.1.1 ∈ U ∧ (z.1.2,z.2) ∈ O})
    (u : P) (hu : u ∈ U) (y : Ep×Es) (hy : y ∈ O)
    (tau C : ℝ) (htau : 0 < tau) (hC : 0 ≤ C)
    (hpair : ∀ v ∈ U, ∀ k ≤ 2,
      tau^k*‖iteratedFDeriv ℝ k (fun x => f v x-f u x) y‖ ≤
        C*tau*(‖v‖+‖u‖)*‖v-u‖) :
    HasFDerivAt (fun v => fderiv ℝ (fun x => f v (y.1,x)) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fun x => f v (y.1,x)) y.2) u) u ∧
    ‖fderiv ℝ (fun v => fderiv ℝ (fun x => f v (y.1,x)) y.2) u‖ ≤ 2*C*‖u‖ := by
  let Ω : Set ((P×Ep)×Es) := {z | z.1.1 ∈ U ∧ (z.1.2,z.2) ∈ O}
  have hΩ : IsOpen Ω := (hU.preimage continuous_fst.fst).inter
    (hO.preimage (continuous_fst.snd.prodMk continuous_snd))
  have hyΩ : ((u,y.1),y.2) ∈ Ω := ⟨hu,hy⟩
  have hfs (v : P) (hv : v ∈ U) : ContDiffOn ℝ ∞ (f v) O := by
    exact hjoint.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun x hx => ⟨hv,hx⟩)
  have hjet := (incrementsJointSpatialJets_bridge
    (fun z : (P×Ep)×Es => f z.1.1 (z.1.2,z.2)) Ω hΩ hjoint).2.1
  have hfirst : ContDiffAt ℝ ∞ (fun v => fderiv ℝ (fun x => f v (y.1,x)) y.2) u :=
    (hjet.contDiffAt (hΩ.mem_nhds hyΩ)).comp u
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)
  have hD := (hfirst.differentiableAt (by simp)).hasFDerivAt
  refine ⟨hD,?_⟩
  apply round4_hasFDerivAt_le_of_quadratic_difference _ U u (hU.mem_nhds hu) C hC _ _ hD
  intro v hv
  have hdiff : ContDiffOn ℝ ∞ (fun x => f v x-f u x) O := (hfs v hv).sub (hfs u hu)
  have hb := spatial_first_jet_le hO hdiff hy 0
  simp only [norm_iteratedFDeriv_zero,Nat.zero_add] at hb
  have hs (w : P) (hw : w ∈ U) : DifferentiableAt ℝ (fun x => f w (y.1,x)) y.2 :=
    (((hfs w hw).contDiffAt (hO.mem_nhds hy)).comp y.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  rw [fderiv_fun_sub (hs v hv) (hs u hu)] at hb
  have hj := (mul_le_mul_of_nonneg_left hb htau.le).trans (by
    simpa only [pow_one] using hpair v hv 1 (by omega))
  have he : C*tau*(‖v‖+‖u‖)*‖v-u‖ = tau*(C*(‖v‖+‖u‖)*‖v-u‖) := by ring
  rw [he] at hj
  exact (mul_le_mul_iff_right₀ htau).mp hj

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_background_first_of_fast_difference
