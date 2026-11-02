import Probes.Round4PrescribedModeBinding
import Probes.ActualIncrementPrimaryNativePhysical

/-!
# The actual prescribed first mode has the physical metric residual

This specializes the original finite-solver cancellation to `(8.3)`, after
an actual phase-adapted chart has been chosen.  Primitive cutoff and legal
normal-field jets produce the source budget internally.  In particular, no
bound on the desired reconstructed displacement or metric residual is assumed.
The output is the linearized metric of the *same* sine/cosine mode identified
in `Round4PrescribedModeBinding`, with the finite accuracy gain retained.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance prescribedTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Actual physical cancellation for a prescribed legal mode. The constant
is independent of `u`, `delta`, `tau`, and `ell`; the primitive geometry,
fixed weight, solver length and observed order are displayed explicitly. -/
theorem round4_prescribed_mode_physical_residual
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (c : Ep → D → M) (hc : c = fun b x => (chart b).symm x)
    (psi chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c b x))
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (c z.1 z.2)))
    (hfree : ∀ z ∈ O,
      let b := incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ)
      (b.comp b.adjoint).IsInvertible)
    (hlegal : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ)
      (nu z.1 z.2) = 0)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta lam Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hadapted : EqOn (fun z : X => lam*psi z) (fun z => z.2 0) O)
    (hBRb : ∀ a ≤ n, ∀ z ∈ S, ell^a * ‖iteratedFDeriv ℝ a
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hAb : ∀ a ≤ n, ∀ z ∈ S, ell^a * ‖iteratedFDeriv ℝ a
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ a ≤ n, ∀ z ∈ S, ell^a * ‖iteratedFDeriv ℝ a
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hchib : ∀ a ≤ n, ∀ z ∈ O, ell^a * ‖iteratedFDeriv ℝ a chi z‖ ≤ Bchi)
    (hnub : ∀ a ≤ n, ∀ z ∈ O, ell^a *
      ‖iteratedFDeriv ℝ a (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (u : Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let W := fun z : X => round4ActualProbeMode label l (F z.1) (hF z.1) (c z.1)
      (vf z.1) (fun x => lam*psi (z.1,x)) tau length u z.2
    let E := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => W (z.1,x)) z.2
    let K := probeNormalAmplitudeConstant n lam Bchi Bnu
    ContDiffOn ℝ ∞ W O ∧ ContDiffOn ℝ ∞ E O ∧
      ∀ a ≤ j, ∀ z ∈ S, tau^a * ‖iteratedFDeriv ℝ a E z‖ ≤
        actualPrimaryPhysicalCost m N n length j Mg K K * (tau/ell)^length *
          (delta*tau)*‖u‖ := by
  intro vf W E K
  have hell : 0 < ell := htau.trans_le htaul
  have hvf := actualProbeNormalAmplitude_weighted_jets F c chi nu O hO hchi hnu n
    ell delta tau lam Bchi Bnu hell.le hdelta htau.le hBchi hBnu hchib hnub
  have hK : 0 ≤ K := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  let vfR := fun (b : Ep) (x : D) => u (label (l,false)) • vf b x
  let vfI := fun (b : Ep) (x : D) => (-u (label (l,true))) • vf b x
  have hvR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O :=
    hvf.1.const_smul _
  have hvI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O :=
    hvf.1.const_smul _
  have hscaled (v : ℝ) (hv : |v| ≤ ‖u‖) : ∀ a ≤ n, ∀ z ∈ S,
      ell^a * ‖iteratedFDeriv ℝ a (fun w : X => (v • vf w.1 w.2 : V)) z‖ ≤
        K*((delta*tau)*‖u‖) := by
    intro a ha z hz
    rw [iteratedFDeriv_const_smul_apply'
      ((hvf.1.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp)),norm_smul,Real.norm_eq_abs]
    calc
      _ = |v| * (ell^a*‖iteratedFDeriv ℝ a (fun w : X => (vf w.1 w.2 : V)) z‖) := by ring
      _ ≤ |v| * (K*(delta*tau)) :=
        mul_le_mul_of_nonneg_left (hvf.2 a ha z (hSO hz)) (abs_nonneg _)
      _ ≤ ‖u‖*(K*(delta*tau)) :=
        mul_le_mul_of_nonneg_right hv (mul_nonneg hK (mul_nonneg hdelta htau.le))
      _ = _ := by ring
  have hkr : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ) (vfR z.1 z.2) = 0 := by
    intro z hz
    exact actualProbeNormalAmplitude_transverse_kernel F hF c chi nu delta tau lam z
      (hlegal z hz) _
  have hki : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 a.succ) (vfI z.1 z.2) = 0 := by
    intro z hz
    exact actualProbeNormalAmplitude_transverse_kernel F hF c chi nu delta tau lam z
      (hlegal z hz) _
  have hp := actual_primary_native_physical_weighted_jets F hF chart hchart c hc O S hO hSO
    hOt hinj hfree vfR vfI hvR hvI hkr hki hBR hA hB hG hJ hT n length j horder
    tau ell Mg K K ((delta*tau)*‖u‖) htau htaul hell1 hMg hK hK
    (mul_nonneg (mul_nonneg hdelta htau.le) (norm_nonneg _)) hBRb hAb hBb
    (hscaled _ (norm_le_pi_norm u _))
    (hscaled _ (by simpa only [abs_neg,Real.norm_eq_abs] using norm_le_pi_norm u (label (l,true))))
  dsimp only at hp
  let W0 := fun z : X => round4ActualProbeMode label l (F z.1) (hF z.1) (c z.1)
    (vf z.1) (fun x => x 0) tau length u z.2
  have hmode (b : Ep) := round4ActualProbeMode_eq_full_reconstruction label l
    (F b) (hF b) (c b) (vf b) (fun x => x 0) tau length u
  have hW0 : ContDiffOn ℝ ∞ W0 O := by
    apply hp.1.congr
    intro z hz
    exact congrFun (hmode z.1) z.2
  have hWW : EqOn W W0 O := by
    intro z hz
    simp only [W,W0,round4ActualProbeMode,actualRealHomogeneousProbe,
      actualReconstructedWave,actualTrigModulation,Bool.false_eq_true,ite_false,ite_true,
      hadapted hz]
  have hEE : EqOn E (fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => W0 (z.1,x)) z.2) O := by
    intro z hz
    have heq : (fun x => W (z.1,x)) =ᶠ[𝓝 z.2] (fun x => W0 (z.1,x)) :=
      eventuallyEq_of_mem ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
        (fun x hx => hWW hx)
    simp only [E,actualCoordinateMetricLinearization,heq.fderiv_eq]
  have hE0 : ContDiffOn ℝ ∞ (fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => W0 (z.1,x)) z.2) O := by
    convert hp.2.1 using 1
    funext z
    congr 1
    funext x
    exact congrFun (hmode z.1) x
  refine ⟨hW0.congr hWW,hE0.congr hEE,?_⟩
  intro a ha z hz
  have he : E =ᶠ[𝓝 z] (fun w : X => actualCoordinateMetricLinearization (F w.1 ∘ c w.1)
      (fun x => W0 (w.1,x)) w.2) :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => hEE hw)
  rw [(he.iteratedFDeriv ℝ a).eq_of_nhds]
  have hb := hp.2.2 a ha z hz
  convert hb using 1
  · congr 3
    funext w
    congr 1
    funext x
    exact congrFun (hmode w.1) x
  · ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_prescribed_mode_physical_residual
