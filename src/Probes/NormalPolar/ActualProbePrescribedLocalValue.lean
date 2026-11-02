import NormalPolar.ActualProbePrescribedLocalHessian
import Probes.Round4PrescribedModeValue
import Probes.Round4PrescribedGlobalColumns
import Probes.Round4PrescribedModePrincipal

/-!
# Original prescribed responses with carrier-local phases

The complete actual global field, physical source, observed chart and
principal term are unchanged. The global Hessian/column regularity now
comes from the actual amplitude support and phase germs on each carrier's
open chart. No smooth extension of any inactive phase is required.
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

theorem round4_global_actual_value_principal_error_local_phase
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
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
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
    let C := actualRealHomogeneousConstant m N 2 length Mg
      (homogeneousSourceConstant m N (2+length+1) MB
        (probeNormalAmplitudeConstant (2+length+1) weight Bchi Bnu)) Mpsi
    ∀ (u : Pspace) (sine : Bool),
      ‖fderiv ℝ (fun v => wave v x) u (Pi.single (label (i,sine)) 1)-
        (if sine then actualProbeSinColumn delta tau weight psi amplitude x
          else actualProbeCosColumn delta tau weight psi amplitude x)‖ ≤
        (delta*tau)*(tau/ell)*C := by
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
  have hs := round4_actual_homogeneous_source_smooth (F b) (hF b) (c i b) vphys O hBRs hvs
  have hmode_resp (u : Pspace) (sine : Bool) :
      fderiv ℝ (fun v => modeLocal v x) u (Pi.single (label (i,sine)) 1) =
        modeLocal (Pi.single (label (i,sine)) 1) x := by
    let J := probeColumnMap (fun q => modeLocal (Pi.single q 1) x)
    have heq : (fun v => modeLocal v x) = J := by
      funext v
      simpa only [J, modeLocal, probeColumnMap_apply, finiteProbeSource] using
        round4ActualProbeMode_finite_source label i (F b) (hF b) (c i b) vphys
          (fun y => weight*psi y) tau length O hO hAs hBs hs v x hxO
    rw [heq,J.hasFDerivAt.fderiv,probeColumnMap_apply]
    simp [Pi.single_apply]
  have hresp (u : Pspace) (sine : Bool) :
      fderiv ℝ (fun v => wave v x) u (Pi.single (label (i,sine)) 1) =
        fderiv ℝ (fun v => modeLocal v x) u (Pi.single (label (i,sine)) 1) := by
    have hg := round4PrescribedGlobalWave_response_column label F hF c vf phase tau length a
      hA hB hBR hvf u (b,c i b x) (label (i,sine))
    rw [hg,hmode_resp]
    exact (hcolumn sine).eq_of_nhds
  have hlocal := round4_actual_single_mode_value_principal_error label i delta tau ell weight psi
    F hF (c i) chi nu length b (a i).target S (a i).open_target hS hpsi (hBR i) hchi hnu
    hAs hBs hGs hJs hTs MB Mg Bchi Bnu Mpsi hdelta hell hell1 htau htaul hMB hMg hBchi hBnu
    hBRb hchib hnub hAb hBb hGb hJb hTb hpsib x hx hweight
  intro u sine
  rw [hresp u sine]
  exact hlocal u sine

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_global_actual_value_principal_error_local_phase
