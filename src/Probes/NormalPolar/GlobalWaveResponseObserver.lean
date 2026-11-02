import NormalPolar.GlobalWaveResponseFirstJet

noncomputable section
set_option backward.isDefEq.respectTransparency false
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


variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual global prescribed wave, observed through any genuine smooth
source transition, has the native paired Hessian response required on an
original atlas. Both transition jets and the same physical amplitude are
retained. No response estimate is supplied as a hypothesis. -/
theorem globalWave_native_hessian_principal_observer
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
    (x : D) (hx : x ∈ S)
    (φ : Z → D) (O : Set Z) (hO : IsOpen O)
    (hφ : ContDiffOn ℝ ∞ φ O)
    (hmap : MapsTo φ O ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (z : Z) (hz : z ∈ O) (hzx : φ z = x) :
    let amplitude := fun y => chi (b,y) • (nu b y : V)
    let wave := fun u y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label u) (b,c i b (φ y))
    let CH := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    let C1 := actualPrescribedProbeJetConstant m N p 1 length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg
    ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) z) u (Pi.single (i,sine) 1) -
        ((delta/tau)*probeTrig sine (weight*psi x/tau)) •
          phaseRankOneHessian (psi ∘ φ) (amplitude ∘ φ) z‖ ≤
        (delta/tau)*((tau/ell)*CH*‖fderiv ℝ φ z‖^2 +
          tau*C1*‖fderiv ℝ (fderiv ℝ φ) z‖) := by
  intro amplitude wave CH C1 u sine
  let Osrc := (fun y : D => (b,y)) ⁻¹' (a i).target
  have hOsrc : IsOpen Osrc := (a i).open_target.preimage (continuous_const.prodMk continuous_id)
  have hxO : x ∈ Osrc := hS x hx
  have hOW : ∀ y ∈ Osrc, (b,c i b y) ∈ W := by
    intro y hy
    have hh := hsourceW ((a i).map_target hy)
    simpa only [hinverse (b,y) hy] using hh
  let G := fun (u : ProbeParameters r) y => round4PrescribedGlobalWave label F hF c vf phase tau
    length a (probeParameterEmbedding label u) (b,c i b y)
  have hGW := round4_prescribed_global_wave_joint_smooth_local_phase label F hF c vf phase tau length a
    W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
  have hparam : ContMDiff 𝓘(ℝ,ProbeParameters r) 𝓘(ℝ,Fin p → ℝ) ∞
      (probeParameterEmbedding label) :=
    (probeParameterEmbedding label).toContinuousLinearMap.contDiff.contMDiff
  have hfst : ContMDiffOn 𝓘(ℝ, ProbeParameters r × D) 𝓘(ℝ, ProbeParameters r) ∞
      (Prod.fst : ProbeParameters r × D → ProbeParameters r) (Set.univ ×ˢ Osrc) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ProbeParameters r × D) 𝓘(ℝ, D) ∞
      (Prod.snd : ProbeParameters r × D → D) (Set.univ ×ˢ Osrc) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hcoords : ContMDiffOn 𝓘(ℝ,ProbeParameters r × D)
      ((𝓘(ℝ,Fin p → ℝ)).prod ((𝓘(ℝ,Ep)).prod I)) ∞
      (fun q : ProbeParameters r × D => (probeParameterEmbedding label q.1,(b,c i b q.2)))
      (Set.univ ×ˢ Osrc) :=
    (hparam.comp_contMDiffOn hfst).prodMk
      (contMDiffOn_const.prodMk (hobs.comp hsnd (fun q hq => hq.2)))
  have hGsmooth : ContDiffOn ℝ ∞ (Function.uncurry G) (Set.univ ×ˢ Osrc) := by
    have hh := hGW.comp hcoords (fun q hq => ⟨mem_univ _,hOW q.2 hq.2⟩)
    exact hh.contDiffOn
  have hb := globalWave_native_hessian_principal_paired label F hF c vf phase tau length a W K hW hK hKsource hchart
    hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
    hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
    hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
    hAb hBb hGb hJb hTb hpsib x hx u sine
  have hfirst := globalWave_native_first_response_paired label F hF c vf phase tau length a W K hW hK hKsource hchart
    hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
    hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
    hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
    hAb hBb hGb hJb hTb hpsib x hx u sine
  change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v)) x) u (Pi.single (i,sine) 1) -
    ((delta/tau)*probeTrig sine (weight*psi x/tau)) • phaseRankOneHessian psi amplitude x‖ ≤
      (delta/tau)*(tau/ell)*CH at hb
  change ‖fderiv ℝ (fun y => fderiv ℝ (fun v => G v y) u (Pi.single (i,sine) 1)) x‖ ≤
    delta*C1 at hfirst
  have he : 0 ≤ (delta/tau)*(tau/ell)*CH := (norm_nonneg _).trans hb
  have hθ : DifferentiableAt ℝ psi (φ z) := by
    rw [hzx]
    exact (hpsi.contDiffAt (hOsrc.mem_nhds hxO)).differentiableAt (by simp)
  have htransport := globalWave_actual_parameter_hessian_error_change_coordinates
    isOpen_univ hOsrc hO G φ hGsmooth hφ hmap psi amplitude u (Pi.single (i,sine) 1)
    (mem_univ _) z hz ((delta/tau)*probeTrig sine (weight*psi x/tau))
    ((delta/tau)*(tau/ell)*CH) he hθ (by simpa only [hzx] using hb)
  change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) z) u (Pi.single (i,sine) 1) -
    ((delta/tau)*probeTrig sine (weight*psi x/tau)) •
      phaseRankOneHessian (psi ∘ φ) (amplitude ∘ φ) z‖ ≤ _ at htransport
  apply htransport.trans
  rw [hzx]
  calc
    _ ≤ ((delta/tau)*(tau/ell)*CH)*‖fderiv ℝ φ z‖^2 +
        (delta*C1)*‖fderiv ℝ (fderiv ℝ φ) z‖ := by
      gcongr
    _ = _ := by field_simp [htau.ne']

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_hessian_principal_observer
