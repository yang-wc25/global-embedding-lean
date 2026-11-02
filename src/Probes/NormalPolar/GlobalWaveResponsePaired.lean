import NormalPolar.ActualProbePrescribedLocalPrincipal
import NormalPolar.ActualProbePrescribedLocalValue
import NormalPolar.GlobalWaveResponseCharts
import Probes.Round4PrescribedGlobalPrincipal
import Probes.Round4PrescribedGlobalValue
import Probes.Round4OriginalProbeParameters

/-! Actual full globally extended waves on the original paired Pi parameters.
The primitive geometry and the physical source binding are consumed by the
existing actual global construction. This file derives the actual paired
Hessian/value response, retaining the same map and all source domains. -/
noncomputable section
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private noncomputable local instance pairedHessianSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance pairedHessianNorm :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance pairedHessianSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

/-- Canonical reindexing is literally the established zero-extension map.
This identifies the supplied global-wave model without changing any ball. -/
theorem globalWave_original_parameter_map_eq (r : ℕ) :
    (probeParameterEmbedding (round4PairedParameterIndex r).toEmbedding :
        ProbeParameters r → (Fin (Fintype.card (Fin r × Bool)) → ℝ)) =
      round4PairedParameterReindex r := by
  funext u j
  obtain ⟨q,rfl⟩ := (round4PairedParameterIndex r).surjective j
  change Function.extend (round4PairedParameterIndex r) u 0
    (round4PairedParameterIndex r q) = _
  rw [(round4PairedParameterIndex r).injective.extend_apply]
  exact (round4PairedParameterReindex_apply_label u q).symm



/-- The actual global-wave Hessian column, in the literal original paired
parameter direction. There is no dimension-dependent parameter norm loss. -/
theorem globalWave_native_hessian_principal_paired
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
    let wave := fun u y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label u) (b,c i b y)
    let C := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single (i,sine) 1) -
        ((delta/tau)*probeTrig sine (weight*psi x/tau)) •
          phaseRankOneHessian psi amplitude x‖ ≤ (delta/tau)*(tau/ell)*C := by
  intro amplitude wave C u sine
  have hb := round4_global_actual_hessian_principal_error_local_phase label F hF c vf phase tau length a W K hW hK hKsource hchart
    hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
    hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
    hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
    hAb hBb hGb hJb hTb hpsib x hx
  let O := (fun y : D => (b,y)) ⁻¹' (a i).target
  have hO : IsOpen O := (a i).open_target.preimage (continuous_const.prodMk continuous_id)
  have hxO : x ∈ O := hS x hx
  have hOW : ∀ y ∈ O, (b,c i b y) ∈ W := by
    intro y hy
    have hh := hsourceW ((a i).map_target hy)
    simpa only [hinverse (b,y) hy] using hh
  have hd := (round4_prescribed_global_hessian_parameter_response_local_phase label F hF c vf phase tau
    length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
    b (c i b) O hO hobs hOW (probeParameterEmbedding label u) x hxO).2.differentiableAt
  change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
    (fun y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (b,c i b y))) x) u (Pi.single (i,sine) 1) -
      ((delta/tau)*probeTrig sine (weight*psi x/tau)) •
        phaseRankOneHessian psi amplitude x‖ ≤ _
  rw [fderiv_probeParameterEmbedding_single label
    (fun v => fderiv ℝ (fderiv ℝ
      (fun y => round4PrescribedGlobalWave label F hF c vf phase tau length a v
        (b,c i b y))) x) u hd (i,sine)]
  cases sine with
  | false => exact (hb (probeParameterEmbedding label u)).1
  | true => exact (hb (probeParameterEmbedding label u)).2

/-- The complete global-wave value response has its original negative sign
and its squared-weight denominator, for the same literal paired parameters. -/
theorem globalWave_native_value_principal_paired
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
    let wave := fun u y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label u) (b,c i b y)
    let C := actualRealHomogeneousConstant m N 2 length Mg
      (homogeneousSourceConstant m N (2+length+1) MB
        (probeNormalAmplitudeConstant (2+length+1) weight Bchi Bnu)) Mpsi
    ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => wave v x) u (Pi.single (i,sine) 1) -
        (-(delta*tau)*(weight^2)⁻¹ * probeTrig sine (weight*psi x/tau)) • amplitude x‖ ≤
        (delta*tau)*(tau/ell)*C := by
  intro amplitude wave C u sine
  have hb := round4_global_actual_value_principal_error_local_phase label F hF c vf phase tau length a W K hW hK hKsource hchart
    hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
    hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
    hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
    hAb hBb hGb hJb hTb hpsib x hx
  have hd := (round4PrescribedGlobalWave_hasFDerivAt label F hF c vf phase tau length a
    hA hB hBR hvf (probeParameterEmbedding label u) (b,c i b x)).differentiableAt
  change ‖fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a
    (probeParameterEmbedding label v) (b,c i b x)) u (Pi.single (i,sine) 1) - _‖ ≤ _
  rw [fderiv_probeParameterEmbedding_single label
    (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,c i b x))
    u hd (i,sine)]
  have hh := hb (probeParameterEmbedding label u) sine
  cases sine <;> simpa only [actualProbeSinColumn,actualProbeCosColumn,probeFastPhase_eq,
    Bool.false_eq_true,ite_false,ite_true,probeTrig,amplitude,C,smul_smul,div_eq_mul_inv,neg_mul,mul_assoc] using hh

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_hessian_principal_paired
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_value_principal_paired
