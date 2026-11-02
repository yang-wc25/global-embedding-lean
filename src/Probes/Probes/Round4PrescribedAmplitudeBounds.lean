import Probes.Round4PrescribedSourceBudget
import Probes.Round4PrescribedReconstructedColumns
import Probes.ActualJointHomogeneousReconstruction

/-!
# Scale-uniform value and first derivative bounds for the complete amplitudes

Only primitive cutoff, normal and original geometric coefficient jets enter.
The original finite solver supplies the actual reconstructed correction. Both
complete amplitude channels have size delta*tau*norm(u) and their true joint
first derivative has size delta*norm(u), with a displayed scale-independent
constant and no factor equal to the parameter-space dimension.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

def round4PrescribedAmplitudeCost (m N n length : ℕ) (imag : Bool)
    (lam Mg Bchi Bnu : ℝ) : ℝ :=
  let K := probeNormalAmplitudeConstant n lam Bchi Bnu
  K + 2 * actualJointHomogeneousReconstructionCost m 1 Mg *
    ‖if imag then incrementsModeImagPart (m := m) else incrementsModeRealPart (m := m)‖ *
    homogeneousSourceConstant m N n Mg K *
    ∑ a ∈ Finset.range length, (2*2^n*Mg)^a

theorem round4PrescribedAmplitudeCost_nonneg (m N n length : ℕ) (imag : Bool)
    (lam : ℝ) {Mg Bchi Bnu : ℝ} (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) :
    0 ≤ round4PrescribedAmplitudeCost m N n length imag lam Mg Bchi Bnu := by
  have hK := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  have hS := homogeneousSourceConstant_nonneg m N n hMg hK
  have hR := actualJointHomogeneousReconstructionCost_nonneg m 1 hMg
  unfold round4PrescribedAmplitudeCost
  positivity

theorem round4_prescribed_amplitude_value_first_bounds
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (n length : ℕ) (horder : 2+length ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 a : V)) O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (tau ell delta lam Mg Bchi Bnu : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ 1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ 1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ 1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
    (hchib : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ n, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let A := fun (u : Fin p → ℝ) (z : X) =>
      round4PrescribedAmplitude imag label l (F z.1) (hF z.1) (c z.1) (vf z.1) tau length u z.2
    let C := round4PrescribedAmplitudeCost m N n length imag lam Mg Bchi Bnu
    ∀ u, ContDiffOn ℝ ∞ (A u) O ∧ ∀ z ∈ S,
      ‖A u z‖ ≤ C*delta*tau*‖u‖ ∧ ‖fderiv ℝ (A u) z‖ ≤ C*delta*‖u‖ := by
  intro vf A C u
  have hell : 0 < ell := htau.trans_le htaul
  let K := probeNormalAmplitudeConstant n lam Bchi Bnu
  let Ks := homogeneousSourceConstant m N n Mg K
  let channel : Cdata →L[ℝ] D := if imag then incrementsModeImagPart else incrementsModeRealPart
  let Profile : ℝ := ∑ a ∈ Finset.range length, (2*2^n*Mg)^a
  let Kr := 2*actualJointHomogeneousReconstructionCost m 1 Mg*‖channel‖*Ks*Profile
  have hK : 0 ≤ K := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  have hKs : 0 ≤ Ks := homogeneousSourceConstant_nonneg m N n hMg hK
  have hRC := actualJointHomogeneousReconstructionCost_nonneg m 1 hMg
  have hProfile : 0 ≤ Profile := by unfold Profile; positivity
  have hKr : 0 ≤ Kr := by unfold Kr; positivity
  have hv := actualProbeNormalAmplitude_weighted_jets F c chi nu O hO hchi hnu n
    ell delta tau lam Bchi Bnu hell.le hdelta htau.le hBchi hBnu hchib hnub
  have hs := actualProbeHomogeneousSource_weighted_jets F hF c chi nu O hO hBR hchi hnu n
    ell delta tau lam Mg Bchi Bnu hell.le hdelta htau.le hMg hBchi hBnu hBRb hchib hnub
  let s := actualHomogeneousSource F hF c vf
  let su := fun z : X => actualPairedNormalSource label l (F z.1) (hF z.1) (c z.1) (vf z.1) u z.2
  have hsu : su = finiteProbeSource (pairedProbeSourceDictionary label l s) u := by
    funext z
    exact congrFun (actualPairedNormalSource_eq_finite_source label l (F z.1) (hF z.1)
      (c z.1) (vf z.1) u) z.2
  have hsuj := round4_paired_source_weighted_jets label l s O S hO hSO hs.1 n ell
    (Ks*(delta*tau)) hell.le (fun k hk z hz => hs.2 k hk z (hSO hz)) u
  rw [← hsu] at hsuj
  have hp := actual_joint_finite_channel_reconstruction F hF c su channel n length 1 horder
    O S hO hSO hA hB hG hJ hT hsuj.1 tau ell Mg (2*(Ks*(delta*tau))*‖u‖)
    htau htaul hell1 hMg (by positivity) hAb hBb hGb hJb hTb hsuj.2
  dsimp only at hp
  let R := fun z : X => incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1)
    channel tau length (fun x => su (z.1,x)) z.2
  have hR : ContDiffOn ℝ ∞ R O := hp.2.1
  have hRjet (k : ℕ) (hk : k ≤ 1) (z : X) (hz : z ∈ S) :
      ell^(k+1)*‖iteratedFDeriv ℝ k R z‖ ≤ Kr*delta*tau^2*‖u‖ := by
    apply (hp.2.2 k hk z hz).trans_eq
    dsimp only [Kr]
    ring
  let a := if imag then -u (label (l,true)) else u (label (l,false))
  have ha : ‖a‖ ≤ ‖u‖ := by cases imag <;> simp only [a,ite_false,ite_true,norm_neg] <;> exact norm_le_pi_norm u _
  have hfree : ContDiffOn ℝ ∞ (fun z : X => a • (vf z.1 z.2 : V)) O := hv.1.const_smul a
  have hAeq : A u = fun z : X => a • (vf z.1 z.2 : V) + R z := rfl
  rw [hAeq]
  refine ⟨hfree.add hR,?_⟩
  intro z hz
  have hv0 : ‖(vf z.1 z.2 : V)‖ ≤ K*delta*tau := by
    simpa only [pow_zero,norm_iteratedFDeriv_zero,one_mul,mul_assoc] using hv.2 0 (by omega) z (hSO hz)
  have hv1 : ‖fderiv ℝ (fun w : X => (vf w.1 w.2 : V)) z‖ ≤ K*delta := by
    apply (mul_le_mul_iff_right₀ hell).mp
    calc
      _ ≤ K*(delta*tau) := by
        simpa only [pow_one,norm_iteratedFDeriv_one] using hv.2 1 (by omega) z (hSO hz)
      _ ≤ K*delta*ell := by nlinarith [mul_nonneg hK hdelta]
      _ = _ := by ring
  have hR0 : ‖R z‖ ≤ Kr*delta*tau*‖u‖ := by
    apply (mul_le_mul_iff_right₀ hell).mp
    calc
      _ ≤ Kr*delta*tau^2*‖u‖ := by
        simpa only [zero_add,pow_one,norm_iteratedFDeriv_zero] using hRjet 0 (by omega) z hz
      _ ≤ (Kr*delta*tau*‖u‖)*ell := by
        convert mul_le_mul_of_nonneg_left htaul (show 0 ≤ Kr*delta*tau*‖u‖ by positivity) using 1 <;> ring
      _ = _ := by ring
  have hR1 : ‖fderiv ℝ R z‖ ≤ Kr*delta*‖u‖ := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hell)).mp
    calc
      _ ≤ Kr*delta*tau^2*‖u‖ := by
        simpa only [norm_iteratedFDeriv_one] using hRjet 1 (by omega) z hz
      _ ≤ (Kr*delta*‖u‖)*ell^2 := by
        convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htau.le htaul 2)
          (show 0 ≤ Kr*delta*‖u‖ by positivity) using 1 <;> ring
      _ = _ := by ring
  constructor
  · calc
      _ ≤ ‖a • (vf z.1 z.2 : V)‖+‖R z‖ := norm_add_le _ _
      _ ≤ ‖u‖*(K*delta*tau)+Kr*delta*tau*‖u‖ :=
        add_le_add (by rw [norm_smul]; exact mul_le_mul ha hv0 (norm_nonneg _) (norm_nonneg _)) hR0
      _ = _ := by dsimp only [C,round4PrescribedAmplitudeCost,Kr,K,Ks,channel,Profile]; ring
  · rw [fderiv_fun_add ((hfree.contDiffAt (hO.mem_nhds (hSO hz))).differentiableAt (by simp))
      ((hR.contDiffAt (hO.mem_nhds (hSO hz))).differentiableAt (by simp)),
      fderiv_fun_const_smul ((hv.1.contDiffAt (hO.mem_nhds (hSO hz))).differentiableAt (by simp))]
    calc
      _ ≤ ‖a • fderiv ℝ (fun w : X => (vf w.1 w.2 : V)) z‖+‖fderiv ℝ R z‖ := norm_add_le _ _
      _ ≤ ‖u‖*(K*delta)+Kr*delta*‖u‖ :=
        add_le_add (by rw [norm_smul]; exact mul_le_mul ha hv1 (norm_nonneg _) (norm_nonneg _)) hR1
      _ = _ := by dsimp only [C,round4PrescribedAmplitudeCost,Kr,K,Ks,channel,Profile]; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4PrescribedAmplitudeCost_nonneg
#print axioms GlobalEmbedding.Continuation.round4_prescribed_amplitude_value_first_bounds
