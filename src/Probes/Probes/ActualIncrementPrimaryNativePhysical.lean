import Probes.ActualIncrementPrimaryPhysicalJets
import Probes.ActualSecondaryTensorNaturality
import GlobalEmbedding.Paper.IncrementsModeJointLocalReconstruction

/-! The same full primary sine/cosine displacement has a small genuine native
linearized metric tensor. The actual finite residual is remodulated before
assembling its real bilinear tensor; every spatial slot is preserved. Joint
smoothness of the constructed wave and its physical residual are conclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)


private local instance primaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance primaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance primaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def actualPrimaryPhysicalCost (m N n length j : ℕ) (Mg KR KI : ℝ) : ℝ :=
  2 * ‖parameterRound2_meanTensorAssembly (m+1)‖ * incrementsFastMultiplierConstant j 1 *
    (2*2^n*Mg)^length * homogeneousSourceConstant m N n Mg (KR+KI)

theorem actualPrimaryPhysicalCost_nonneg (m N n length j : ℕ) {Mg KR KI : ℝ}
    (hMg : 0 ≤ Mg) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) :
    0 ≤ actualPrimaryPhysicalCost m N n length j Mg KR KI := by
  have hs := homogeneousSourceConstant_nonneg m N n hMg (add_nonneg hKR hKI)
  have hf := (incrementsFastMultiplierConstant_pos j 1).le
  unfold actualPrimaryPhysicalCost
  positivity

theorem actual_primary_native_physical_weighted_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (c : Ep → D → M) (hc : c = fun b x => (chart b).symm x)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) (c z.1 z.2)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (vfR vfI : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c b x))
    (hvfR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O)
    (hkernelR : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ) (vfR z.1 z.2) = 0)
    (hkernelI : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ) (vfI z.1 z.2) = 0)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ (c z.1)) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (n length j : ℕ) (horder : j+length ≤ n) (tau ell Mg KR KI a : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hell1 : ell ≤ 1) (hMg : 0 ≤ Mg) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) (ha : 0 ≤ a)
    (hBRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hvfRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (vfR w.1 w.2 : V)) z‖ ≤ KR*a)
    (hvfIb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (vfI w.1 w.2 : V)) z‖ ≤ KI*a) :
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
    let W := actualSecondaryModulation (fun z : X => z.2 0) tau ZR ZI
    let E := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => W (z.1,x)) z.2
    ContDiffOn ℝ ∞ W O ∧ ContDiffOn ℝ ∞ E O ∧ ∀ r ≤ j, ∀ z ∈ S,
      tau^r * ‖iteratedFDeriv ℝ r E z‖ ≤
        actualPrimaryPhysicalCost m N n length j Mg KR KI * (tau/ell)^length*a := by
  subst c
  let c : Ep → D → M := fun b => (chart b).symm
  intro source U ZR ZI W E
  have hell : 0 < ell := htau.trans_le htaul
  have hs := (actual_primary_two_channel_source_weighted_jets F hF c vfR vfI
    O S hO hSO hBR hvfR hvfI n ell Mg KR KI a hell.le hMg hKR hKI ha hBRb hvfRb hvfIb).1
  have hZZ := incrementsModeFullReconstruction_joint_contDiffOn F hF c
    (fun _ _ _ => 0) (fun _ _ _ => 0) vfR vfI length tau O hO hG hJ hT hA hB
    contDiffOn_const contDiffOn_const hvfR hvfI hs
  have hZR : ContDiffOn ℝ ∞ ZR O := hZZ.1
  have hZI : ContDiffOn ℝ ∞ ZI O := hZZ.2
  have hphase : ContDiffOn ℝ ∞ (fun z : X => z.2 0) O :=
    (actualSecondaryCoordinatePhase (Ep := Ep) (m := m)).contDiff.contDiffOn
  have hW : ContDiffOn ℝ ∞ W O :=
    actualSecondaryModulation_contDiffOn _ tau ZR ZI O hphase hZR hZI
  let WR := fun b x => WithLp.toLp 2 (fun q : Fin N =>
    (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
      ((ZR (b,x) q : ℂ)+Complex.I*(ZI (b,x) q : ℂ))).re)
  let WI := fun b x => WithLp.toLp 2 (fun q : Fin N =>
    (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
      ((ZR (b,x) q : ℂ)+Complex.I*(ZI (b,x) q : ℂ))).im)
  let err := fun (z : X) i k => Complex.exp (-((z.2 0/tau : ℝ) : ℂ)*Complex.I)*
    ((incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WR z.1) z.2
      (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) : ℂ)+Complex.I*
      (incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WI z.1) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) : ℂ))
  have he := actual_primary_physical_error_weighted_jets F hF chart hchart O S hO hSO hOt hinj hfree
    vfR vfI hvfR hvfI hkernelR hkernelI hBR hA hB n length tau ell Mg KR KI a htau hell hell1
    hMg hKR hKI ha hBRb hAb hBb hvfRb hvfIb
  let Kerr := 2*(2*2^n*Mg)^length*(tau/ell)^length*
    (homogeneousSourceConstant m N n Mg (KR+KI)*a)
  have hKerr : 0 ≤ Kerr := by
    have hc := homogeneousSourceConstant_nonneg m N n hMg (add_nonneg hKR hKI)
    dsimp only [Kerr]
    positivity
  have her : ContDiffOn ℝ ∞ err O := he.1
  have heb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r err z‖ ≤ Kerr := by
    intro r hr z hz
    exact (he.2 r (by omega) z hz).trans_eq (by dsimp only [Kerr]; ring)
  have hp : ∀ k < j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) (fun w : X => w.2 0) z‖ ≤ 1 := by
    intro k _ z _
    exact actual_linear_phase_slow_jets (actualSecondaryCoordinatePhase (Ep := Ep) (m := m))
      (actualSecondaryCoordinatePhase_norm_le (Ep := Ep) (m := m)) ell z k
  obtain ⟨hTensor,hTensorb⟩ := actual_remodulated_physical_tensor_weighted_jets err
    (fun z : X => z.2 0) O S hO hSO her hphase j tau ell 1 Kerr htau htaul hell1 hKerr hp heb
  have heq : EqOn E (actualRemodulatedPhysicalTensor err (fun z : X => z.2 0) tau) O := by
    intro z hz
    apply actual_bilinear_tensor_eq_of_basis
    intro i k
    have hFcs : ContDiffOn ℝ ∞ (F z.1 ∘ c z.1) (chart z.1).target :=
      ((hF z.1).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hchart z.1))).contDiffOn
    have hFc : DifferentiableAt ℝ (F z.1 ∘ c z.1) z.2 :=
      (hFcs.contDiffAt ((chart z.1).open_target.mem_nhds (hOt z hz))).differentiableAt (by simp)
    have hWs := (actual_joint_contDiffOn_slice W O hW z.1).contDiffAt
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    change actualCoordinateMetricLinearization _ _ _ _ _ = _
    rw [actual_coordinate_metric_linearization_eq_variation _ _ _ _ _ hFc
      (hWs.differentiableAt (by simp)), actualRemodulatedPhysicalTensor_basis]
    have hreal : WR z.1 = fun x => W (z.1,x) := by
      funext x
      exact congrFun (increments_primary_real_mode_eq (fun x : D => x 0) tau
        (fun x => ZR (z.1,x)) (fun x => ZI (z.1,x))) x
    dsimp only [err]
    have hc := actual_complex_demodulated_residual_real (z.2 0/tau)
      (incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WR z.1) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single k 1))
      (incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WI z.1) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)) 0
    simpa only [sub_zero,mul_zero,Complex.zero_re,hreal] using hc.symm
  refine ⟨hW,hTensor.congr heq,?_⟩
  intro r hr z hz
  have hg : E =ᶠ[𝓝 z] actualRemodulatedPhysicalTensor err (fun z : X => z.2 0) tau :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
  exact (hTensorb r hr z hz).trans_eq (by dsimp only [Kerr,actualPrimaryPhysicalCost]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualPrimaryPhysicalCost_nonneg
#print axioms GlobalEmbedding.Continuation.actual_primary_native_physical_weighted_jets
