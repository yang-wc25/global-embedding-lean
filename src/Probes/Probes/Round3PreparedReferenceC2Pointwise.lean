import Probes.Round3PreparedReferenceCarrier
import Smoothing.Round3OuterReferenceFrameStability
import Smoothing.ParameterRound2OriginalInputs
import Probes.ActualIncrementFreeNormalKernel

/-! Original C2 closeness supplies the actual new first/transverse/free-normal
reserves on every fixed reference cutoff carrier over K. The threshold is
chosen before the perturbed map. Original samples, chart jets, reference
normal membership/unit/kernel and slice identities are derived internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance pointwiseFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance pointwiseFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance pointwiseHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance pointwiseHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance

theorem round3_prepared_reference_C2_pointwise
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Data.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : Ep → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => F z.1 z.2-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => F z.1 z.2-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ epsilon →
    ∀ nu a y, y ∈ tsupport (packet.piece nu a).cutoff → y.1 ∈ Data.parameterSet →
      let z := actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (packet.piece nu a).native y
      let e := (packet.piece nu a).slices
      (∀ v : D, (packet.cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, (packet.cT/4)*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2) ∧
      (1/2 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2)
        (Data.freeNormal nu ((Data.parameterChart baseIndex.2).symm z.1,(e z.1).symm z.2))‖ := by
  obtain ⟨epsilon,hepsilon,hStable⟩ := round3_original_C2_reference_frame_stability
    (m := m) (d := d) (N := N) (M := M) (P := Ep) (c := Data.parameterCount)
    packet.Tchart packet.Tchart_nonneg packet.cF packet.cT packet.MH
    packet.cF_pos packet.cT_pos packet.MH_nonneg
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound nu a y hy hKy z e
  let part := packet.piece nu a
  let c := Data.atlas.chart part.host
  let b := part.native
  let aa := actualHostAdaptedChart c b
  have hys : y ∈ aa.source := part.support hy
  rcases part.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hz : z ∈ b.target := by rw [← hat]; exact aa.map_source hys
  have hzp : z.1 = y.1 := (hforw y hys).1
  have hZK : z.1 ∈ Data.parameterSet := hzp ▸ hKy
  have hsp := actual_host_slice_source_point c b _ part.slices part.data z hz
  have hact0 := part.active _ hsp
  have hact : (z.1,(e z.1).symm z.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hact0
  have hEq : actualOriginalOpenParameterSlice Data baseIndex z.1 = fun x => Data.F (z.1,x) := by
    rw [actualOriginalOpenParameterSlice_eq Data baseIndex z.1 hact0.2.1]
    funext x
    change Data.F ((Data.parameterChart baseIndex.2).symm z.1,x) = _
    rw [hId]
    rfl
  have hFirst : ∀ v : D, packet.cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Data.F (z.1,x)) ∘ (e z.1).symm) z.2 v‖^2 := by
    simpa only [hEq] using packet.first nu a z hz
  have hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)) :=
    fun p => hF0joint.comp (contMDiff_const.prodMk contMDiff_id)
  have hFrame : ∀ v : Tdata, packet.cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F (z.1,x)) (hF0 z.1) (e z.1).symm z.2 v‖^2 := by
    have hh := packet.transverse nu a z hz
    simpa only [hEq] using hh
  have hHessian : ‖fderiv ℝ (fderiv ℝ ((fun x => Data.F (z.1,x)) ∘ (e z.1).symm)) z.2‖ ≤ packet.MH := by
    simpa only [hEq] using packet.hessian nu a z hz
  have hCoord0 := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas Data.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Data.F (by simpa only [modelWithCornersSelf_prod] using hF0joint)
  have hCoord := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas Data.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth (Function.uncurry F) (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  rcases actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem part.host) b
    (fun w : Ep × M => Data.phase nu ((Data.parameterChart baseIndex.2).symm w.1,w.2))
    part.slices part.data with ⟨hSource,hBS,hBIS,hPoint,hTransition,hReverse,hMap,hAdapt⟩
  have hCarrier := round3_prepared_reference_carrier_sampling Data hd hs hn baseIndex hId hOne packet nu a y hy hKy
  obtain ⟨normal,hNormal,hUnit,hKernel⟩ := round3_prepared_primary_reference_normal
    Data hd hs hn baseIndex hId packet nu a z hz (hF0 z.1)
  have hh := hStable Data.atlas Data.parameterChart Data.F (Function.uncurry F) hF0 hF S
    (fun _ _ hy => hy.1) hCoord0 hCoord hFinite hBound (part.host,baseIndex.2) e b.target b.open_target
    hTransition (fun z hz => (hPoint z hz).2) (by intro w hw; rw [hId]; exact mem_univ _)
    z hz (hPoint z hz).1 (he z.1) hCarrier.1 (fun j _ _ => hCarrier.2 j)
  dsimp only at hh
  have hParamId : (Data.parameterChart baseIndex.2).symm z.1 = z.1 := by rw [hId]; rfl
  rw [hParamId] at hh
  simp only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]
  have hResult := hh hFirst hFrame hHessian normal hUnit hKernel
  simpa only [Function.uncurry,hNormal,e] using hResult

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_C2_pointwise
