import Probes.Round4PrescribedAmplitudeBounds
import Probes.ActualIncrementJointDirectionalJets

/-!
# Every slow spatial/auxiliary jet of the complete prescribed amplitudes

Only primitive cutoff, normal and original geometric coefficient jets enter.
The original finite solver supplies the actual reconstructed correction. Both complete amplitude channels have weighted jets of size delta*tau*norm(u),
with a displayed scale-independent constant and no parameter-dimension factor.
This supplies the spatial-jet input for the genuine two-parameter mean difference.
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

def round4PrescribedAmplitudeJetCost (m N n length j : ℕ) (imag : Bool)
    (lam Mg Bchi Bnu : ℝ) : ℝ :=
  let K := probeNormalAmplitudeConstant n lam Bchi Bnu
  K + 2 * actualJointHomogeneousReconstructionCost m j Mg *
    ‖if imag then incrementsModeImagPart (m := m) else incrementsModeRealPart (m := m)‖ *
    homogeneousSourceConstant m N n Mg K *
    ∑ a ∈ Finset.range length, (2*2^n*Mg)^a


theorem round4PrescribedAmplitudeJetCost_nonneg (m N n length j : ℕ) (imag : Bool)
    (lam : ℝ) {Mg Bchi Bnu : ℝ} (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) :
    0 ≤ round4PrescribedAmplitudeJetCost m N n length j imag lam Mg Bchi Bnu := by
  have hK := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  have hS := homogeneousSourceConstant_nonneg m N n hMg hK
  have hR := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  unfold round4PrescribedAmplitudeJetCost
  positivity


theorem round4_prescribed_amplitude_all_weighted_jets
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (n length j : ℕ) (horder : j+1+length ≤ n)
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
    (hGb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
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
    let C := round4PrescribedAmplitudeJetCost m N n length j imag lam Mg Bchi Bnu
    ∀ u, ContDiffOn ℝ ∞ (A u) O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (A u) z‖ ≤ C*delta*tau*‖u‖ := by
  intro vf A C u
  have hell : 0 < ell := htau.trans_le htaul
  let K := probeNormalAmplitudeConstant n lam Bchi Bnu
  let Ks := homogeneousSourceConstant m N n Mg K
  let channel : Cdata →L[ℝ] D := if imag then incrementsModeImagPart else incrementsModeRealPart
  let Profile : ℝ := ∑ a ∈ Finset.range length, (2*2^n*Mg)^a
  let Kr := 2*actualJointHomogeneousReconstructionCost m j Mg*‖channel‖*Ks*Profile
  have hK : 0 ≤ K := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  have hKs : 0 ≤ Ks := homogeneousSourceConstant_nonneg m N n hMg hK
  have hRC := actualJointHomogeneousReconstructionCost_nonneg m j hMg
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
  have hp := actual_joint_finite_channel_reconstruction F hF c su channel n length j horder
    O S hO hSO hA hB hG hJ hT hsuj.1 tau ell Mg (2*(Ks*(delta*tau))*‖u‖)
    htau htaul hell1 hMg (by positivity) hAb hBb hGb hJb hTb hsuj.2
  dsimp only at hp
  let R := fun z : X => incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1)
    channel tau length (fun x => su (z.1,x)) z.2
  have hR : ContDiffOn ℝ ∞ R O := hp.2.1
  have hRjet (k : ℕ) (hk : k ≤ j) (z : X) (hz : z ∈ S) :
      ell^(k+1)*‖iteratedFDeriv ℝ k R z‖ ≤ Kr*delta*tau^2*‖u‖ := by
    apply (hp.2.2 k hk z hz).trans_eq
    dsimp only [Kr]
    ring
  let a := if imag then -u (label (l,true)) else u (label (l,false))
  have ha : ‖a‖ ≤ ‖u‖ := by cases imag <;> simp only [a,ite_true,norm_neg] <;> exact norm_le_pi_norm u _
  have hfree : ContDiffOn ℝ ∞ (fun z : X => a • (vf z.1 z.2 : V)) O := hv.1.const_smul a
  have hAeq : A u = fun z : X => a • (vf z.1 z.2 : V) + R z := rfl
  rw [hAeq]
  refine ⟨hfree.add hR,?_⟩
  intro k hk z hz
  have hvb : ell^k*‖iteratedFDeriv ℝ k (fun z : X => a • (vf z.1 z.2 : V)) z‖ ≤
      K*delta*tau*‖u‖ := by
    rw [iteratedFDeriv_const_smul_apply'
      ((hv.1.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)),norm_smul]
    calc
      _ = ‖a‖*(ell^k*‖iteratedFDeriv ℝ k (fun w : X => (vf w.1 w.2 : V)) z‖) := by ring
      _ ≤ ‖u‖*(K*(delta*tau)) :=
        mul_le_mul ha (hv.2 k (by omega) z (hSO hz)) (by positivity) (norm_nonneg _)
      _ = _ := by ring
  have hRb : ell^k*‖iteratedFDeriv ℝ k R z‖ ≤ Kr*delta*tau*‖u‖ := by
    apply (mul_le_mul_iff_right₀ hell).mp
    calc
      _ = ell^(k+1)*‖iteratedFDeriv ℝ k R z‖ := by rw [pow_succ]; ring
      _ ≤ Kr*delta*tau^2*‖u‖ := hRjet k hk z hz
      _ ≤ (Kr*delta*tau*‖u‖)*ell := by
        convert mul_le_mul_of_nonneg_left htaul
          (show 0 ≤ Kr*delta*tau*‖u‖ by positivity) using 1 <;> ring
      _ = _ := by ring
  have hadd := actual_joint_slow_add_jet_bound (fun z : X => a • (vf z.1 z.2 : V)) R
    k ell (K*delta*tau*‖u‖) (Kr*delta*tau*‖u‖) hell.le z
    ((hfree.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hR.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)) hvb hRb
  apply hadd.trans_eq
  dsimp only [C,round4PrescribedAmplitudeJetCost,Kr,K,Ks,channel,Profile]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_prescribed_amplitude_all_weighted_jets
