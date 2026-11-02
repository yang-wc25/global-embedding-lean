import NormalPolar.GlobalWaveResponseSupport

/-!
# Actual complete wave response on every original atlas support

All transition constants are chosen from the fixed charts and closed wave
carriers before any scale, auxiliary family, or probe parameter is supplied.
On the carrier the true coordinate chain rule is used, with both transition
jets. Off the carrier the complete global response has a zero germ. The
principal phase and amplitude are the same global fields in both branches.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {E M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,E) M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "IM" => 𝓘(ℝ,E)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private noncomputable local instance atlasHessianSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance atlasHessianNorm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance atlasHessianSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

/-- Fixed geometry supplies the whole original-atlas native Hessian
response constants before all actual construction data and scales. The
remaining hypotheses describe primitive jets and exact physical identities;
none supplies a native response or transition-derivative estimate. -/
theorem exists_uniform_globalWave_originalAtlas_response
    (atlas : BufferedAtlas M E) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j))
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn IM 𝓘(ℝ,D) ∞ (source l) (source l).source)
    (carrier : Fin r → Set M) (hclosed : ∀ l, IsClosed (carrier l))
    (hcarrier : ∀ l, carrier l ⊆ (source l).source) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧
    ∀
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    (i : Fin r) (b : Ep) (chi : X → ℝ)
    (nu : (t : Ep) → (y : D) → normalSpace (I := IM) (F t) (c i t y))
    (delta ell weight : ℝ) (psi : D → ℝ)
    (hphysical : vf i = actualProbeNormalAmplitude F (c i) chi nu delta tau weight)
    (hinverse : ∀ z ∈ (a i).target, (a i).symm z = (z.1,c i z.1 z.2))
    (hsourceW : (a i).source ⊆ W)
    (hobs : ContMDiffOn 𝓘(ℝ,D) IM ∞ (c i b) ((fun y : D => (b,y)) ⁻¹' (a i).target))
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
      (fun y => (normalSpace (I := IM) (F b) (c i b y)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (c i b) y)) y‖ ≤ Mg)
    (hTb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeTransverseValue (F b) (c i b)) y‖ ≤ Mg)
    (hpsib : ∀ k < 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) (fun y => weight*psi y) y‖ ≤ Mpsi)
    (theta : M → ℝ) (amplitude : M → V)
    (hamplitudeZero : ∀ y, y ∉ carrier i → amplitude y = 0)
    (hcoordinate : ∀ y ∈ (source i).target, c i b y = (source i).symm y)
    (hsourceTarget : ∀ y ∈ (source i).target, (b,y) ∈ (a i).target)
    (hpsiOriginal : ∀ y ∈ (source i).target, psi y = theta ((source i).symm y))
    (hamplitudeOriginal : ∀ y ∈ (source i).target,
      chi (b,y) • (nu b y : V) = amplitude ((source i).symm y))
    (hsamples : ∀ j y, y ∈ atlas.support j → y ∈ carrier i → source i y ∈ S)
    (hsliceW : ∀ y, (b,y) ∈ W)
    (hactualCarrier : ∀ q ∈ K i, q.2 ∈ carrier i),
    let CH := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    let C1 := actualPrescribedProbeJetConstant m N p 1 length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg
    ∀ (j : Fin atlas.count) (x : M), x ∈ atlas.support j →
      ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (fun y =>
          round4PrescribedGlobalWave label F hF c vf phase tau length a
            (probeParameterEmbedding label v) (b,(atlas.chart j).symm y))) (atlas.chart j x))
          u (Pi.single (i,sine) 1) -
        ((delta/tau)*probeTrig sine (weight*theta x/tau)) •
          phaseRankOneHessian (theta ∘ (atlas.chart j).symm)
            (amplitude ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
        (delta/tau)*((tau/ell)* |CH| *B1^2 + tau* |C1| *B2) := by
  obtain ⟨B1,B2,hB1,hB2,htrans⟩ := exists_uniform_globalWaveAtlasTransition_jets
    atlas hAtlas hcompact source hsource carrier hclosed hcarrier
  refine ⟨B1,B2,hB1,hB2,?_⟩
  intro label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf
    hinput hphase i b chi nu delta ell weight psi hphysical hinverse hsourceW hobs hphaseChart
    hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi hdelta hell hell1 htau htaul hweight
    hMB hMg hBchi hBnu hBRb hchib hnub hAb hBb hGb hJb hTb hpsib
    theta amplitude hamplitudeZero hcoordinate hsourceTarget hpsiOriginal hamplitudeOriginal
    hsamples hsliceW hactualCarrier CH C1 j x hx u sine
  let z := atlas.chart j x
  let phi := globalWaveAtlasTransition atlas source j i
  let O := ((atlas.chart j).symm.trans (source i)).source
  let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a
    (probeParameterEmbedding label v) (b,(atlas.chart j).symm y)
  have hxsource := hAtlas.support_subset j hx
  have hz : z ∈ (atlas.chart j).target := (atlas.chart j).map_source hxsource
  have hxback : (atlas.chart j).symm z = x := (atlas.chart j).left_inv hxsource
  have hnonneg : 0 ≤ (delta/tau)*((tau/ell)* |CH| *B1^2 + tau* |C1| *B2) := by positivity
  by_cases hk : x ∈ carrier i
  · have hxi := hcarrier i hk
    have hzO : z ∈ O := by
      change z ∈ (atlas.chart j).target ∧ (atlas.chart j).symm z ∈ (source i).source
      exact ⟨hz,by simpa only [hxback] using hxi⟩
    have hO : IsOpen O := ((atlas.chart j).symm.trans (source i)).open_source
    have hphi : ContDiffOn ℝ ∞ phi O :=
      globalWaveAtlasTransition_contDiffOn atlas hAtlas source hsource j i
    have hmap : MapsTo phi O ((fun y : D => (b,y)) ⁻¹' (a i).target) := by
      intro y hy
      change y ∈ (atlas.chart j).target ∧ (atlas.chart j).symm y ∈ (source i).source at hy
      exact hsourceTarget _ ((source i).map_source hy.2)
    have hphiz : phi z = source i x := by
      simp only [phi,globalWaveAtlasTransition,Function.comp_apply,hxback]
    have hpoint (y : E) (hy : y ∈ O) : c i b (phi y) = (atlas.chart j).symm y := by
      change y ∈ (atlas.chart j).target ∧ (atlas.chart j).symm y ∈ (source i).source at hy
      change c i b (source i ((atlas.chart j).symm y)) = (atlas.chart j).symm y
      rw [hcoordinate _ ((source i).map_source hy.2)]
      exact (source i).left_inv hy.2
    have hprincipal := globalWave_native_hessian_principal_observer label F hF c vf phase tau length a W K hW hK hKsource hchart
      hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
      hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
      hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
      hAb hBb hGb hJb hTb hpsib (source i x) (hsamples j x hx hk)
      phi O hO hphi hmap z hzO hphiz u sine
    let localWave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (b,c i b (phi y))
    have hfamily (v : ProbeParameters r) : localWave v =ᶠ[𝓝 z] wave v := by
      filter_upwards [hO.mem_nhds hzO] with y hy
      dsimp only [localWave,wave]
      rw [hpoint y hy]
    have hhessian : (fun v => fderiv ℝ (fderiv ℝ (localWave v)) z) =
        (fun v => fderiv ℝ (fderiv ℝ (wave v)) z) := by
      funext v
      exact (hfamily v).fderiv.fderiv_eq
    have hphasegerm : (psi ∘ phi) =ᶠ[𝓝 z] (theta ∘ (atlas.chart j).symm) := by
      filter_upwards [hO.mem_nhds hzO] with y hy
      change y ∈ (atlas.chart j).target ∧ (atlas.chart j).symm y ∈ (source i).source at hy
      change psi (source i ((atlas.chart j).symm y)) = theta ((atlas.chart j).symm y)
      rw [hpsiOriginal _ ((source i).map_source hy.2),(source i).left_inv hy.2]
    have hamp : ((fun y => chi (b,y) • (nu b y : V)) ∘ phi) z =
        (amplitude ∘ (atlas.chart j).symm) z := by
      change chi (b,phi z) • (nu b (phi z) : V) = amplitude ((atlas.chart j).symm z)
      rw [hphiz,hamplitudeOriginal _ ((source i).map_source hxi),(source i).left_inv hxi,hxback]
    have htensor : phaseRankOneHessian (psi ∘ phi)
        ((fun y => chi (b,y) • (nu b y : V)) ∘ phi) z =
        phaseRankOneHessian (theta ∘ (atlas.chart j).symm)
          (amplitude ∘ (atlas.chart j).symm) z := by
      unfold phaseRankOneHessian
      rw [hphasegerm.fderiv_eq,hamp]
    have hpsiPoint : psi (source i x) = theta x := by
      rw [hpsiOriginal _ ((source i).map_source hxi),(source i).left_inv hxi]
    change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (localWave v)) z) u (Pi.single (i,sine) 1) -
      ((delta/tau)*probeTrig sine (weight*psi (source i x)/tau)) •
        phaseRankOneHessian (psi ∘ phi) ((fun y => chi (b,y) • (nu b y : V)) ∘ phi) z‖ ≤
      (delta/tau)*((tau/ell)*CH*‖fderiv ℝ phi z‖^2 + tau*C1*‖fderiv ℝ (fderiv ℝ phi) z‖) at hprincipal
    rw [hhessian,htensor,hpsiPoint] at hprincipal
    apply hprincipal.trans
    have hjets := htrans j i x hx hk
    change ‖fderiv ℝ phi z‖ ≤ B1 ∧ ‖fderiv ℝ (fderiv ℝ phi) z‖ ≤ B2 at hjets
    calc
      _ ≤ (delta/tau)*((tau/ell)* |CH| *‖fderiv ℝ phi z‖^2 +
          tau* |C1| *‖fderiv ℝ (fderiv ℝ phi) z‖) := by
        gcongr <;> exact le_abs_self _
      _ ≤ _ := by
        gcongr
        · exact hjets.1
        · exact hjets.2
  · have heta : ContMDiffOn 𝓘(ℝ,E) ((𝓘(ℝ,Ep)).prod IM) ∞
        (fun y => (b,(atlas.chart j).symm y)) (atlas.chart j).target :=
      contMDiffOn_const.prodMk (contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem j))
    have hn : (b,(atlas.chart j).symm z) ∉ K i := by
      intro hh
      apply hk
      simpa only [hxback] using hactualCarrier _ hh
    have hzero := (globalWave_native_response_zero_off_carrier label F hF c vf phase tau length a W K hW hK
      hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
      (fun y => (b,(atlas.chart j).symm y)) (atlas.chart j).target (atlas.chart j).open_target
      heta (fun y _ => hsliceW _) z hz u i sine hn).2
    have hamp : (amplitude ∘ (atlas.chart j).symm) z = 0 := by
      simpa only [Function.comp_apply,hxback] using hamplitudeZero x hk
    have htensor : phaseRankOneHessian (theta ∘ (atlas.chart j).symm)
        (amplitude ∘ (atlas.chart j).symm) z = 0 := by
      simp only [phaseRankOneHessian,hamp,ContinuousLinearMap.smulRight_zero]
    change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) z) u (Pi.single (i,sine) 1) -
      ((delta/tau)*probeTrig sine (weight*theta x/tau)) •
        phaseRankOneHessian (theta ∘ (atlas.chart j).symm)
          (amplitude ∘ (atlas.chart j).symm) z‖ ≤ _
    rw [hzero,htensor,smul_zero,sub_zero,norm_zero]
    exact hnonneg

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.exists_uniform_globalWave_originalAtlas_response
