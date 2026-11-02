import Probes.Round4PrescribedModeBinding
import Probes.ActualFullProbeHessianBounds
import Probes.ActualPrimitiveTwoJetBounds

/-!
# Actual prescribed first block: exact Hessian principal terms and slow error

The original complete first block is differentiated in its actual parameter
columns after the true spatial Hessian. Its cosine/sine principal terms retain
chi*nu and dpsi squared. Every source, free-amplitude and phase two-jet budget
needed for the slow error is produced from primitive profiles by existing
proved modules; no source/reconstruction/Hessian-remainder estimate is an input.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

private local instance prescribedPrincipalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedPrincipalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedPrincipalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

def round4PrescribedHessianErrorConstant (m N order : ℕ)
    (weight Mphase Bchi Bnu : Fin r → ℝ) (MB Mg : ℝ) (i : Fin r) : ℝ :=
  let n := 2+order+1
  let K := 2^n*Bchi i*Bnu i
  let P := Mphase i/weight i
  K/(weight i)^2+(2*P*K+P*K)/weight i +
    ∑ l, actualRealHomogeneousConstant m N 2 order Mg
      (homogeneousSourceConstant m N n MB (probeNormalAmplitudeConstant n (weight l) (Bchi l) (Bnu l)))
      (Mphase l)

theorem round4_actual_prescribed_hessian_principal_error
    (label : (Fin r × Bool) ↪ Fin p) (delta tau ell : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (order : ℕ) (b : Ep) (Ojoint : Set X) (S : Set D)
    (hOjoint : IsOpen Ojoint) (hS : ∀ x ∈ S, (b, x) ∈ Ojoint)
    (hphaseSmooth : ∀ l, ContDiffOn ℝ ∞ (phase l) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hBrow : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) Ojoint)
    (hchi : ∀ l, ContDiffOn ℝ ∞ (chi l) Ojoint)
    (hnu : ∀ l, ContDiffOn ℝ ∞ (fun z : X ↦ (nu l z.1 z.2 : V)) Ojoint)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) y))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) (F b) (chart b y)).subtypeL.comp
      (incrementsModeCoordinateJ (F b) (hF b) (chart b) y)) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue (F b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (MB Mg : ℝ) (Bchi Bnu Mphase : Fin r → ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htauell : tau ≤ ell) (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg)
    (hBchi : ∀ l, 0 ≤ Bchi l) (hBnu : ∀ l, 0 ≤ Bnu l)
    (hBrowb : ∀ a ≤ 2 + order + 1, ∀ z ∈ Ojoint, ell ^ a * ‖iteratedFDeriv ℝ a
      (fun y : X ↦ fun i : Fin (m + 1) ↦
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ l a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (chi l) z‖ ≤ Bchi l)
    (hnub : ∀ l a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (fun y : X ↦ (nu l y.1 y.2 : V)) z‖ ≤ Bnu l)
    (hAb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hBb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hGb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) (F b) (chart b z)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (chart b) z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue (F b) (chart b)) y‖ ≤ Mg)
    (hphase : ∀ l a, a < 2 → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a + 1) (fun z ↦ weight l * phase l z) y‖ ≤ Mphase l) 
    (x : D) (hx : x ∈ S) (i : Fin r) (hw : 0 < weight i) :
    let amplitude := fun l y => chi l (b,y) • (nu l b y : V)
    let W := actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b
    let C := round4PrescribedHessianErrorConstant m N order weight Mphase Bchi Bnu MB Mg i
    ∀ u : Fin p → ℝ,
      (‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (W w)) x) u
        (Pi.single (label (i,false)) 1) -
        ((delta/tau)*Real.cos (weight i*phase i x/tau)) •
          phaseRankOneHessian (phase i) (amplitude i) x‖ ≤ (delta/tau)*(tau/ell)*C) ∧
      (‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (W w)) x) u
        (Pi.single (label (i,true)) 1) -
        ((delta/tau)*Real.sin (weight i*phase i x/tau)) •
          phaseRankOneHessian (phase i) (amplitude i) x‖ ≤ (delta/tau)*(tau/ell)*C) := by
  intro amplitude W C
  let n := 2+order+1
  let O := (fun y => (b,y)) ⁻¹' Ojoint
  have hO : IsOpen O := hOjoint.preimage (continuous_const.prodMk continuous_id)
  have hSO : S ⊆ O := hS
  let k := fun l => actualPrescribedProbeSource label l F hF chart (chi l) (nu l)
    delta tau (weight l) b
  let Ksrc := fun l => homogeneousSourceConstant m N n MB
    (probeNormalAmplitudeConstant n (weight l) (Bchi l) (Bnu l))
  let Kprof := fun l => 2^n*Bchi l*Bnu l
  have hsource l := actualPrescribedProbeSource_weighted_jets label l F hF chart (chi l) (nu l)
    Ojoint hOjoint hBrow (hchi l) (hnu l) n ell delta tau (weight l) MB (Bchi l) (Bnu l)
    hell.le hdelta htau.le hMB (hBchi l) (hBnu l) hBrowb (hchib l) (hnub l) b
  have hprofile l := actualProbeProfile_weighted_jets (chi l) (fun z : X => (nu l z.1 z.2 : V))
    Ojoint hOjoint (hchi l) (hnu l) n ell (Bchi l) (Bnu l) hell.le (hBchi l) (hBnu l)
    (hchib l) (hnub l)
  have hslice l := fixed_parameter_slice_weighted_jets
    (fun z : X => chi l z • (nu l z.1 z.2 : V)) Ojoint hOjoint (hprofile l).1 n ell
    (Kprof l) hell.le (hprofile l).2 b
  have hks (l : Fin r) : 0 ≤ Ksrc l := homogeneousSourceConstant_nonneg m N n hMB
    (probeNormalAmplitudeConstant_nonneg n (weight l) (hBchi l) (hBnu l))
  have hkp (l : Fin r) : 0 ≤ Kprof l := by
    have hc := hBchi l
    have hn := hBnu l
    dsimp only [Kprof]
    positivity
  have hkb : ∀ l q a, a ≤ 2+order+1 → ∀ y ∈ S,
      ell^a*‖iteratedFDeriv ℝ a (k l q) y‖ ≤ Ksrc l*delta*tau := by
    intro l q a ha y hy
    simpa only [mul_assoc] using (hsource l).2 q a ha y (hS y hy)
  have hp2 := probe_profile_twojet_of_weighted (amplitude i) x ell (Kprof i) hell
    (fun a ha => (hslice i).2 a (by dsimp only [n]; omega) x (hS x hx))
  have hph2 := probe_phase_twojet_of_weighted (phase i) x
    (((hphaseSmooth i).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))
    ell (weight i) (Mphase i) hell hw (fun a ha => hphase i a ha x hx)
  have hrem := actualFullProbe_hessian_remainders_bound label delta tau ell weight phase amplitude
    (F b) (hF b) (chart b) order k O S hO hSO hphaseSmooth (fun l => (hslice l).1)
    hA hB hG hJ hT0 (fun l q => (hsource l).1 q) Mg Ksrc Mphase
    hdelta hell hell1 htau htauell hMg hks hAb hBb hGb hJb hT0b hkb hphase
    x hx i hw (Kprof i) (Kprof i) (Kprof i) (Mphase i/weight i) (Mphase i/weight i)
    (hkp i) (hkp i) (hkp i) hph2.1 hph2.1 hp2.1 hp2.2.1 hp2.2.2 hph2.2.1 hph2.2.2
  intro u
  have hcos := actualFullProbe_cos_hessian_response label delta tau weight phase amplitude
    (F b) (hF b) (chart b) order k O hO hphaseSmooth (fun l => (hslice l).1)
    hA hB hG hJ hT0 (fun l q => (hsource l).1 q) u x (hSO hx) i htau.ne' hw.ne'
  have hsin := actualFullProbe_sin_hessian_response label delta tau weight phase amplitude
    (F b) (hF b) (chart b) order k O hO hphaseSmooth (fun l => (hslice l).1)
    hA hB hG hJ hT0 (fun l q => (hsource l).1 q) u x (hSO hx) i htau.ne' hw.ne'
  change (_ ≤ _) ∧ (_ ≤ _)
  constructor
  · change ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ
        (actualFiniteProbeWithReconstruction label delta tau weight phase amplitude (F b) (hF b)
          (chart b) order k w)) x) u (Pi.single (label (i,false)) 1) - _‖ ≤ _
    rw [hcos,add_sub_cancel_left]
    exact hrem.1
  · change ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ
        (actualFiniteProbeWithReconstruction label delta tau weight phase amplitude (F b) (hF b)
          (chart b) order k w)) x) u (Pi.single (label (i,true)) 1) - _‖ ≤ _
    rw [hsin,add_sub_cancel_left]
    exact hrem.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_actual_prescribed_hessian_principal_error
