import NormalPolar.PassiveParameterJets
import NormalPolar.PassiveWaveSeedNativeChart
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The true native transition acquires the identity parameter block. Its
positive-order budget is at most one plus the original transition budget;
the phase itself keeps every original derivative budget unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {S Ep D : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

private theorem passiveWaveSeed_linear_positive_jets
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (ell : ℝ) (k : ℕ) (hk : 1 ≤ k) (z : X) :
    ell^(k-1)*‖iteratedFDeriv ℝ k L z‖ ≤ ‖L‖ := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  cases r with
  | zero =>
    simp only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
    exact le_rfl
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ : X => L := funext (fun y => L.fderiv)
    rw [he,iteratedFDeriv_const_of_ne (by omega : r+1 ≠ 0)]
    simp only [Pi.zero_apply,norm_zero,mul_zero]
    exact L.opNorm_nonneg

theorem passiveWaveSeed_transition_jets
    (f : S × D → S × D) (O : Set (S × D)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (z : Ep × D) (hz : (0,z.2) ∈ O)
    (ell : ℝ) (hell : 0 ≤ ell) (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ell^(k-1)*‖iteratedFDeriv ℝ k f (0,z.2)‖ ≤ T) :
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (fun y : Ep × D => (y.1,(f (0,y.2)).2)) z‖ ≤ 1+T := by
  let L : (Ep × D) →L[ℝ] (S × D) := passiveParameterProjection
  have hsp : ContDiffAt ℝ ∞ (fun y : Ep × D => (f (0,y.2)).2) z :=
    (hf.snd.comp_continuousLinearMap L).contDiffAt
      ((hO.preimage L.continuous).mem_nhds hz)
  have hnorm : ‖iteratedFDeriv ℝ k (fun y : Ep × D => (f (0,y.2)).2) z‖ ≤
      ‖iteratedFDeriv ℝ k f (0,z.2)‖ := by
    rw [passiveParameter_iteratedFDeriv_norm (0 : S) _ O hO hf.snd z hz k (by simp)]
    have hh := (ContinuousLinearMap.snd ℝ S D).norm_iteratedFDeriv_comp_left
      (hf.contDiffAt (hO.mem_nhds hz)) (n := k) (by simp)
    exact hh.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ..)
      (norm_nonneg _)).trans_eq (one_mul _))
  have hfirst : ell^(k-1)*‖iteratedFDeriv ℝ k (fun y : Ep × D => y.1) z‖ ≤ 1 :=
    (passiveWaveSeed_linear_positive_jets (ContinuousLinearMap.fst ℝ Ep D) ell k hk z).trans
      (ContinuousLinearMap.norm_fst_le ..)
  rw [iteratedFDeriv_prodMk (i := k) (contDiffAt_fst : ContDiffAt ℝ ∞ (fun y : Ep × D => y.1) z)
    hsp (by simp),ContinuousMultilinearMap.opNorm_prod,mul_max_of_nonneg _ _ (pow_nonneg hell _)]
  exact max_le (hfirst.trans (le_add_of_nonneg_right hT))
    (((mul_le_mul_of_nonneg_left hnorm (pow_nonneg hell _)).trans hbound).trans
      (le_add_of_nonneg_left zero_le_one))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_transition_jets
