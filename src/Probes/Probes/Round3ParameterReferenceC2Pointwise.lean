import Probes.Round3ParameterReferenceCarrier
import Smoothing.Round3OuterReferenceFrameStability
import Smoothing.ParameterRound2OriginalInputs

/-! A fixed reference primary piece on an arbitrary parameter manifold stays
usable for the SAME physical perturbation under the original joint C2 norm.
The tolerance precedes the new map; all support points are covered, so this
entrance does not shrink the whole parameter domain at any repair stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance pointFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance pointFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance pointHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance pointHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance

theorem round3Parameter_reference_C2_pointwise
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (hK : Ref.parameterSet = univ)
    (hInner : ∀ y ∈ tsupport piece.cutoff, y.2 ∈ Ref.atlas.inner piece.host)
    (hParam : ∀ y ∈ tsupport piece.cutoff, y.1 ∈ Ref.parameterNormDomain ip)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ piece.native.target, ∀ v : D,
      cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Ref.F ((Ref.parameterChart ip).symm z.1,x)) ∘
        (piece.slices z.1).symm) z.2 v‖^2)
    (hFrame : ∀ z ∈ piece.native.target, ∀ v : Tdata,
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (fun x => Ref.F ((Ref.parameterChart ip).symm z.1,x))
        (hF0joint.comp (contMDiff_const.prodMk contMDiff_id)) (piece.slices z.1).symm z.2 v‖^2)
    (hHessian : ∀ z ∈ piece.native.target,
      ‖fderiv ℝ (fderiv ℝ ((fun x => Ref.F ((Ref.parameterChart ip).symm z.1,x)) ∘
        (piece.slices z.1).symm)) z.2‖ ≤ MH)
    (hChartJets : ∀ j y, y ∈ tsupport piece.cutoff →
      ‖iteratedFDeriv ℝ j piece.native.symm
        (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native y)‖ ≤ T j) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ y, y ∈ tsupport piece.cutoff →
      let z := actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native y
      let p := (Ref.parameterChart ip).symm z.1
      (∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, (cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2 v‖^2) ∧
      (1/2 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2)
        (Ref.freeNormal nu (p,(piece.slices z.1).symm z.2))‖ := by
  obtain ⟨epsilon,hepsilon,hStable⟩ := round3_original_C2_reference_frame_stability
    (m := m) (d := d) (N := N) (M := M) (P := P) (c := Ref.parameterCount)
    T hT cF cT MH hcF hcT hMH
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound y hy z p
  let c := Ref.atlas.chart piece.host
  let a := actualHostAdaptedChart c piece.native
  have hys := piece.support hy
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hz : z ∈ piece.native.target := by rw [← hat]; exact a.map_source hys
  have hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Ref.F (p,x)) :=
    fun p => hF0joint.comp (contMDiff_const.prodMk contMDiff_id)
  have hCoord0 := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Ref.F (by simpa only [modelWithCornersSelf_prod] using hF0joint)
  have hCoord := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth (Function.uncurry F) (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  rcases actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem piece.host) piece.native
    (fun w : Ep × M => Ref.phase nu ((Ref.parameterChart ip).symm w.1,w.2))
    piece.slices piece.data with ⟨hSource,hBS,hBIS,hPoint,hTransition,hReverse,hMap,hAdapt⟩
  have hParameter (w : X) (hw : w ∈ piece.native.target) : w.1 ∈ (Ref.parameterChart ip).target := by
    have hsp := actual_host_slice_source_point c piece.native _ piece.slices piece.data w hw
    exact ((round3Parameter_originalNativeOpen_iff Ref (piece.host,ip) _).mp
      (piece.native_source hsp.2)).2.1
  have hSample := round3Parameter_reference_carrier_sampling Ref hd ip nu W piece hK hInner hParam y hy
  obtain ⟨normal,hNormal,hUnit,hKernel⟩ := round3Parameter_reference_primary_normal
    Ref hd hs hn ip nu W piece z hz (hF0 p)
  have hh := hStable Ref.atlas Ref.parameterChart Ref.F (Function.uncurry F) hF0 hF S
    (fun _ _ h => h.1) hCoord0 hCoord hFinite hBound (piece.host,ip) piece.slices
    piece.native.target piece.native.open_target hTransition (fun w hw => (hPoint w hw).2) hParameter
    z hz (hPoint z hz).1 (he z.1) hSample (fun j _ _ => by
      change ‖iteratedFDeriv ℝ j (actualSourceChartTransition (fun _ => c) piece.slices) z‖ ≤ T j
      rw [hbj j z hz]
      exact hChartJets j y hy)
  have hResult := hh (hFirst z hz) (hFrame z hz) (hHessian z hz) normal hUnit hKernel
  simpa only [Function.uncurry,hNormal] using hResult

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_reference_C2_pointwise
