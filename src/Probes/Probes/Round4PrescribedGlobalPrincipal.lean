import Probes.Round4PrescribedGlobalHessian
import Probes.Round4PrescribedGlobalColumns
import Probes.Round4PrescribedModePrincipal

/-!
# Actual global paired Hessian principal terms with primitive slow errors

This is a quantitative endpoint for the SAME complete globally extended field.
The physical source (8.3) of the selected mode is retained by its explicit input
binding. The actual global native parameter-Hessian column is transported to
its original local mode, where primitive profiles give the sigma*tau/ell error.
The source/chart identity and phase identity are primitive chart data, while
all output smoothness, parameter response, and Hessian estimates are produced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ
private local instance globalPrincipalSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalPrincipalNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private local instance globalPrincipalSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

private theorem round4_mode_phase_value_congr
    (label : (Fin r × Bool) ↪ Fin p) (i : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (phi psi : D → ℝ)
    (tau : ℝ) (length : ℕ) (u : Pspace) (x : D) (h : phi x = psi x) :
    round4ActualProbeMode label i F hF c vf phi tau length u x =
      round4ActualProbeMode label i F hF c vf psi tau length u x := by
  simp only [round4ActualProbeMode,actualRealHomogeneousProbe,actualReconstructedWave,
    actualTrigModulation,Bool.false_eq_true,ite_false,ite_true,h]

theorem round4_global_actual_hessian_principal_error
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (i : Fin r) (b : Ep) (chi : X → ℝ)
    (nu : (t : Ep) → (y : D) → normalSpace (I := I) (F t) (c i t y))
    (delta ell weight : ℝ) (psi : D → ℝ)
    (hphysical : vf i = actualProbeNormalAmplitude F (c i) chi nu delta tau weight)
    (hinverse : ∀ z ∈ (a i).target, (a i).symm z = (z.1,c i z.1 z.2))
    (hsourceW : (a i).source ⊆ W)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ (c i b) ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hphaseChart : ∀ y, (b,y) ∈ (a i).target → phase i ((a i).symm (b,y)) = weight*psi y)
    (hpsi : ContDiffOn ℝ ∞ psi ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hchi : ContDiffOn ℝ ∞ chi (a i).target)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) (a i).target)
    (S : Set D) (hS : ∀ y ∈ S, (b,y) ∈ (a i).target)
    (MB Mg Bchi Bnu Mpsi : ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hweight : 0 < weight)
    (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBRb : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fun d : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c i w.1) w.2 0 d : V)) z‖ ≤ MB)
    (hchib : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (hAb : ∀ k ≤ 2+length+1, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hBb : ∀ k ≤ 2+length+1, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hGb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => freeGramRightInverse (fderiv ℝ (F b ∘ c i b) y)) y‖ ≤ Mg)
    (hJb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => (normalSpace (I := I) (F b) (c i b y)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (c i b) y)) y‖ ≤ Mg)
    (hTb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeTransverseValue (F b) (c i b)) y‖ ≤ Mg)
    (hpsib : ∀ k < 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) (fun y => weight*psi y) y‖ ≤ Mpsi)
    (x : D) (hx : x ∈ S) :
    let amplitude := fun y => chi (b,y) • (nu b y : V)
    let wave := fun u y => round4PrescribedGlobalWave label F hF c vf phase tau length a u (b,c i b y)
    let C := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    ∀ u : Pspace,
      (‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single (label (i,false)) 1)-
        ((delta/tau)*Real.cos (weight*psi x/tau)) • phaseRankOneHessian psi amplitude x‖ ≤
          (delta/tau)*(tau/ell)*C) ∧
      (‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single (label (i,true)) 1)-
        ((delta/tau)*Real.sin (weight*psi x/tau)) • phaseRankOneHessian psi amplitude x‖ ≤
          (delta/tau)*(tau/ell)*C) := by
  intro amplitude wave C
  let O := (fun y : D => (b,y)) ⁻¹' (a i).target
  have hO : IsOpen O := (a i).open_target.preimage (continuous_const.prodMk continuous_id)
  have hxO : x ∈ O := hS x hx
  have hOW : ∀ y ∈ O, (b,c i b y) ∈ W := by
    intro y hy
    have hh := hsourceW ((a i).map_target hy)
    simpa only [hinverse (b,y) hy] using hh
  have ht : ContDiffOn ℝ ∞ (fun y : D => (b,y)) O := (contDiff_const.prodMk contDiff_id).contDiffOn
  have hm : MapsTo (fun y : D => (b,y)) O (a i).target := fun _ hy => hy
  have hAs := (hA i).comp ht hm
  have hBs := (hB i).comp ht hm
  have hGs := (hG i).comp ht hm
  have hJs := (hJ i).comp ht hm
  have hTs := (hT i).comp ht hm
  have hBRs := (hBR i).comp ht hm
  let vphys := actualProbeNormalAmplitude F (c i) chi nu delta tau weight b
  have hvs : ContDiffOn ℝ ∞ (fun y => (vphys y : V)) O := by
    have hh := (hvf i).comp ht hm
    rw [hphysical] at hh
    exact hh
  let modeLocal := round4ActualProbeMode label i (F b) (hF b) (c i b) vphys (fun y => weight*psi y) tau length
  have hcolumn (ch : Bool) :
      (wave (Pi.single (label (i,ch)) 1)) =ᶠ[𝓝 x] modeLocal (Pi.single (label (i,ch)) 1) := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    have hh := round4PrescribedGlobalWave_chart_column label F hF c vf phase tau length a i ch (b,y) hy
    rw [hinverse (b,y) hy,hphysical] at hh
    exact hh.trans (round4_mode_phase_value_congr label i (F b) (hF b) (c i b) vphys
      (fun z => phase i ((a i).symm (b,z))) (fun z => weight*psi z) tau length
      (Pi.single (label (i,ch)) 1) y (hphaseChart y hy))
  have hresp (u : Pspace) (ch : Bool) :
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single (label (i,ch)) 1) =
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (modeLocal v)) x) u (Pi.single (label (i,ch)) 1) := by
    have hg := round4_prescribed_global_hessian_response_column label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
      b (c i b) O hO hobs hOW u x hxO (label (i,ch))
    have hl := round4_actual_mode_hessian_response_column label i (F b) (hF b) (c i b) vphys
      (fun y => weight*psi y) tau length O hO hAs hBs hGs hJs hTs hBRs hvs
      (hpsi.const_smul weight) u x hxO (label (i,ch))
    change _ = _ at hg hl
    rw [hg,hl]
    exact ((hcolumn ch).fderiv (𝕜 := ℝ)).fderiv_eq
  have hlocal := round4_actual_single_mode_hessian_principal_error label i delta tau ell weight psi
    F hF (c i) chi nu length b (a i).target S (a i).open_target hS hpsi (hBR i) hchi hnu
    hAs hBs hGs hJs hTs MB Mg Bchi Bnu Mpsi hdelta hell hell1 htau htaul hMB hMg hBchi hBnu
    hBRb hchib hnub hAb hBb hGb hJb hTb hpsib x hx hweight
  intro u
  rw [hresp u false,hresp u true]
  exact hlocal u

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_global_actual_hessian_principal_error
