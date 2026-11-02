import NormalPolar.GlobalWaveResponsePaired

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


/-- The genuine first derivative of each actual parameter-response column
is bounded directly from the same primitive profiles as its Hessian. This
supplies the lower-order term required by a nonlinear observer chart. -/
theorem globalWave_native_first_response_paired
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
    let C := actualPrescribedProbeJetConstant m N p 1 length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg
    let wave := fun u y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label u) (b,c i b y)
    ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun y => fderiv ℝ (fun v => wave v y) u
        (Pi.single (i,sine) 1)) x‖ ≤ delta*C := by
  intro C wave u sine
  let O := (fun y : D => (b,y)) ⁻¹' (a i).target
  have hO : IsOpen O := (a i).open_target.preimage (continuous_const.prodMk continuous_id)
  have hxO : x ∈ O := hS x hx
  have ht : ContDiffOn ℝ ∞ (fun y : D => (b,y)) O :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hm : MapsTo (fun y : D => (b,y)) O (a i).target := fun _ hy => hy
  have hAs := (hA i).comp ht hm
  have hBs := (hB i).comp ht hm
  have hGs := (hG i).comp ht hm
  have hJs := (hJ i).comp ht hm
  have hTs := (hT i).comp ht hm
  let vphys := actualProbeNormalAmplitude F (c i) chi nu delta tau weight b
  let modeLocal := round4ActualProbeMode label i (F b) (hF b) (c i b) vphys
    (fun y => weight*psi y) tau length
  let block := actualPrescribedProbeFirstBlock (round4SingleProbeLabel label i) delta tau
    (fun _ : Fin 1 => weight) (fun _ => psi) F hF (c i) (fun _ => chi) (fun _ => nu) length b
  have hblock : block = modeLocal :=
    round4_singleton_firstBlock_eq_mode label i delta tau weight psi F hF (c i) chi nu length b
  have hresponse (y : D) :
      fderiv ℝ (fun v => wave v y) u (Pi.single (i,sine) 1) =
        round4PrescribedGlobalWave label F hF c vf phase tau length a
          (Pi.single (label (i,sine)) 1) (b,c i b y) := by
    have hd := (round4PrescribedGlobalWave_hasFDerivAt label F hF c vf phase tau length a
      hA hB hBR hvf (probeParameterEmbedding label u) (b,c i b y)).differentiableAt
    change fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (b,c i b y)) u (Pi.single (i,sine) 1) = _
    rw [fderiv_probeParameterEmbedding_single label
      (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,c i b y))
      u hd (i,sine)]
    exact round4PrescribedGlobalWave_response_column label F hF c vf phase tau length a
      hA hB hBR hvf (probeParameterEmbedding label u) (b,c i b y) (label (i,sine))
  have hcolumn : (fun y => fderiv ℝ (fun v => wave v y) u (Pi.single (i,sine) 1))
      =ᶠ[𝓝 x] block (Pi.single (label (i,sine)) 1) := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    rw [hresponse,hblock]
    have hh := round4PrescribedGlobalWave_chart_column label F hF c vf phase tau length a
      i sine (b,y) hy
    rw [hinverse (b,y) hy,hphysical] at hh
    apply hh.trans
    change round4ActualProbeMode label i (F b) (hF b) (c i b) vphys
      (fun z => phase i ((a i).symm (b,z))) tau length (Pi.single (label (i,sine)) 1) y =
      round4ActualProbeMode label i (F b) (hF b) (c i b) vphys
        (fun z => weight*psi z) tau length (Pi.single (label (i,sine)) 1) y
    simp only [round4ActualProbeMode,actualRealHomogeneousProbe,actualReconstructedWave,
      actualTrigModulation,Bool.false_eq_true,ite_false,ite_true,hphaseChart y hy]
  have hb := actualPrescribedProbe_uniform_weighted_jets (round4SingleProbeLabel label i)
    delta tau ell (fun _ : Fin 1 => weight) (fun _ => psi) F hF (c i)
    (fun _ => chi) (fun _ => nu) 1 length b (a i).target S (a i).open_target hS
    (fun _ => hpsi) (hBR i) (fun _ => hchi) (fun _ => hnu) hAs hBs hGs hJs hTs
    MB Mg (fun _ => Bchi) (fun _ => Bnu) (fun _ => Mpsi)
    hdelta hell hell1 htau htaul hMB hMg (fun _ => hBchi) (fun _ => hBnu)
    (fun k hk => hBRb k (by omega))
    (fun _ k hk => hchib k (by omega))
    (fun _ k hk => hnub k (by omega))
    (fun k hk => hAb k (by omega))
    (fun k hk => hBb k (by omega))
    (fun k hk => hGb k (by omega))
    (fun k hk => hJb k (by omega))
    (fun k hk => hTb k (by omega))
    (fun _ k hk => hpsib k (by omega))
  have hv := (hb 1 le_rfl x hx (Pi.single (label (i,sine)) 1)).2
  change tau^1 * ‖iteratedFDeriv ℝ 1 (block (Pi.single (label (i,sine)) 1)) x‖ ≤
    ‖(Pi.single (label (i,sine)) 1 : Fin p → ℝ)‖*(delta*tau)*C at hv
  simp only [pow_one,norm_iteratedFDeriv_one,Pi.norm_single,norm_one,one_mul] at hv
  rw [hcolumn.fderiv_eq]
  nlinarith

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_first_response_paired
