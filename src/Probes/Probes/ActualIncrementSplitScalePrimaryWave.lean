import Probes.ActualIncrementSplitScaleReconstruction
import Probes.ActualIncrementPrimaryFullWave

/-! The same full primary wave with the actual slow-coordinate scales.
The value coefficient B and transverse connection T0 carry one extra ell;
all remaining geometric coefficients are shift0. The final fast wave bound
and field-independent constant are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem actual_primary_full_wave_split_scale_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (c : Ep → D → M)
    (vfR vfI : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (phase : X → ℝ)
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
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hvfR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O)
    (hphase : ContDiffOn ℝ ∞ phase O)
    (tau ell Mg KR KI a Mphase : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) (ha : 0 ≤ a)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hvfRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (vfR w.1 w.2 : V)) z‖ ≤ KR*a)
    (hvfIb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (vfI w.1 w.2 : V)) z‖ ≤ KI*a)
    (hpb : ∀ k < j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ (k+1) phase z‖ ≤ Mphase) :
    let source := fun z : X => actualHomogeneousSource F hF c vfR z +
      Complex.I • actualHomogeneousSource F hF c vfI z
    let U := fun b => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c b))
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c b)) ((tau : ℂ)/Complex.I) length
      (fun x => source (b,x))
    let ZR := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeRealPart ∘ U z.1) (fun _ _ _ => 0) (vfR z.1) z.2
    let ZI := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeImagPart ∘ U z.1) (fun _ _ _ => 0) (vfI z.1) z.2
    let W := actualSecondaryModulation phase tau ZR ZI
    ContDiffOn ℝ ∞ W O ∧ ∀ r ≤ j, ∀ z ∈ S,
      tau^r * ‖iteratedFDeriv ℝ r W z‖ ≤ actualPrimaryFullWaveCost m N n length j Mg KR KI Mphase*a := by
  intro source U ZR ZI W
  have hell : 0 < ell := htau.trans_le htaul
  let Cs := homogeneousSourceConstant m N n Mg (KR+KI)
  let Profile : ℝ := ∑ r ∈ Finset.range length, (2*2^n*Mg)^r
  let Cr := actualJointHomogeneousReconstructionCost m j Mg
  have hCs : 0 ≤ Cs := homogeneousSourceConstant_nonneg m N n hMg (add_nonneg hKR hKI)
  have hProf : 0 ≤ Profile := by unfold Profile; positivity
  have hCr : 0 ≤ Cr := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  obtain ⟨hs,hsb⟩ := actual_primary_two_channel_source_weighted_jets F hF c vfR vfI
    O S hO hSO hBR hvfR hvfI n ell Mg KR KI a hell.le hMg hKR hKI ha hBRb hvfRb hvfIb
  let R := fun (channel : Cdata →L[ℝ] D) (z : X) =>
    incrementsModeReconstruction (F z.1) (hF z.1) (c z.1) (channel ∘ U z.1) z.2
  let K := fun (channel : Cdata →L[ℝ] D) => Cr*‖channel‖*Cs*Profile
  have hK : ∀ channel, 0 ≤ K channel := by intro channel; dsimp only [K]; positivity
  have hR (channel : Cdata →L[ℝ] D) : ContDiffOn ℝ ∞ (R channel) O ∧
      ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (R channel) z‖ ≤ K channel*a := by
    obtain ⟨_,hr,hrb⟩ := actual_increment_joint_finite_channel_split_scale F hF c source channel
      n length j horder O S hO hSO hA hB hG hJ hT hs tau ell Mg (Cs*a)
      htau htaul hell1 hMg (mul_nonneg hCs ha) hAb hBb hGb hJb hTb hsb
    refine ⟨hr,?_⟩
    intro r hr z hz
    have hh : ell^r * ‖iteratedFDeriv ℝ r (R channel) z‖ ≤ K channel*a*(tau/ell) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hell).mpr
      calc
        _ = ell^(r+1) * ‖iteratedFDeriv ℝ r (R channel) z‖ := by rw [pow_succ]; ring
        _ ≤ _ := hrb r hr z hz
        _ = _ := by dsimp only [K,Cr,Profile]; ring
    exact hh.trans (mul_le_of_le_one_right (mul_nonneg (hK channel) ha) ((div_le_one hell).mpr htaul))
  have hZeq (channel : Cdata →L[ℝ] D)
      (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x)) :
      (fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
        (channel ∘ U z.1) (fun _ _ _ => 0) (vf z.1) z.2) =
        (fun z => R channel z+(vf z.1 z.2 : V)) := by
    funext z
    have ht : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) z.2 = 0 := by
      ext q
      simp [incrementsModeTransverseSource]
    simp only [incrementsModeFullReconstruction,ht,map_zero,Submodule.coe_zero,smul_zero,sub_zero]
    rfl
  have hzR : ZR = fun z => R incrementsModeRealPart z+(vfR z.1 z.2 : V) := hZeq _ vfR
  have hzI : ZI = fun z => R incrementsModeImagPart z+(vfI z.1 z.2 : V) := hZeq _ vfI
  have hZR : ContDiffOn ℝ ∞ ZR O := by rw [hzR]; exact (hR _).1.add hvfR
  have hZI : ContDiffOn ℝ ∞ ZI O := by rw [hzI]; exact (hR _).1.add hvfI
  have hZbound (channel : Cdata →L[ℝ] D)
      (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
      (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O)
      (Kv : ℝ) (hvb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w : X => (vf w.1 w.2 : V)) z‖ ≤ Kv*a) :
      ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun w => R channel w+(vf w.1 w.2 : V)) z‖ ≤ (K channel+Kv)*a := by
    intro r hr z hz
    exact (actual_joint_slow_add_jet_bound (R channel) (fun w : X => (vf w.1 w.2 : V))
      r ell _ _ hell.le z ((hR channel).1.contDiffAt (hO.mem_nhds (hSO hz)) |>.of_le (by simp))
      (hvf.contDiffAt (hO.mem_nhds (hSO hz)) |>.of_le (by simp))
      ((hR channel).2 r hr z hz) (hvb r (by omega) z hz)).trans_eq (by ring)
  have hbR : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r ZR z‖ ≤
      (K incrementsModeRealPart+KR)*a := by
    rw [hzR]
    exact hZbound _ vfR hvfR KR hvfRb
  have hbI : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r ZI z‖ ≤
      (K incrementsModeImagPart+KI)*a := by
    rw [hzI]
    exact hZbound _ vfI hvfI KI hvfIb
  refine ⟨actualSecondaryModulation_contDiffOn phase tau ZR ZI O hphase hZR hZI,?_⟩
  have hb := actualSecondaryModulation_weighted_jets j phase ZR ZI O S hO hSO hphase hZR hZI
    tau ell Mphase ((K incrementsModeRealPart+KR)*a) ((K incrementsModeImagPart+KI)*a)
    htau htaul hell1 (by positivity) (by positivity) hpb hbR hbI
  intro r hr z hz
  exact (hb r hr z hz).trans_eq (by dsimp only [K,Cr,Cs,Profile,actualPrimaryFullWaveCost]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_full_wave_split_scale_jets
