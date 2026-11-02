import Smoothing.Round3OuterHostNormalRebound
import Smoothing.Round3OuterComputedStageOriginalInputs
import Probes.Round3PreparedReferenceStableParameterDomains
import Probes.Round3PreparedStablePrimaryCover

/-! Fixed actual reference packet plus original C2 closeness constructs the
new normal stage for the literal same SF/SH, including true domains, all
original normal bounds and original normal legality. Neither stable output
geometry nor new-normal jets are an input. Constants precede the current stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
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
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_exists_reference_C2_actual_normal_stage
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (hF0 : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Data.F)
    (BS0 TS0 BP0 TP0 Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (hGiven : ∀ j, 0 ≤ Given j)
    (hGivenFinite : ∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hGivenBound : ∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget : ℝ) (hbudget : 0 ≤ budget) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (F : Ep × M → Ey)
      (H : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (U : Set Ep) (rho : ℝ), IsOpen U → Data.parameterSet ⊆ U → U ⊆ Data.parameterOpen →
    ∀ (reference : ℕ → ℝ)
      (stage : Round3RepairOriginalSmoothingStage (round3OriginalComputedPositiveData Data F H U rho)
        BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference Given),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ epsilon →
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff _ BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference Given stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    ∃ V : Set Ep, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ U ∧
    ∃ domain : Fin Data.primaryCount → Set (Ep × M),
      Nonempty (Round3RepairNormalRebound (stage.restrictParameter V) normal domain C) := by
  obtain ⟨epsilon,hepsilon,hStable⟩ := round3_prepared_reference_C2_stable_parameter_domains
    Data hd hs hn baseIndex hId hOne packet hF0
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_actual_host_normal_rebound
    (m := m) (d := d) (N := N) (M := M)
    BS0 TS0 BP0 TP0 packet.Tchart packet.Tforward Given hBS0 hTS0 hBP0 hTP0
    packet.Tchart_nonneg packet.Tforward_nonneg hGiven Ds Dp radius hradius r
    budget (packet.cF/16) (packet.cT/16) (1/4) hbudget
    (div_pos packet.cF_pos (by norm_num)) (div_pos packet.cT_pos (by norm_num)) (by norm_num)
  refine ⟨epsilon,hepsilon,C,hC,?_⟩
  intro F H U rho hU hKU hUO reference stage S hFinite hBound hF normal
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    have h := round3_repair_stage_smoothed_map_contMDiff _ BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference Given stage
    rw [modelWithCornersSelf_prod] at h
    exact h
  obtain ⟨V0,hV0,hKV0,hV0packet,b0,e0,hb0,hbi0,he0,hSource0,hTarget0,hParam0,
      hData0,hSupport0,hActive0,hFirst0,hFrame0,hNormal0⟩ :=
    hStable (fun p x => F (p,x)) hFjoint hF hFinite hBound
  let V := V0 ∩ U
  have hV : IsOpen V := hV0.inter hU
  have hKV : Data.parameterSet ⊆ V := fun p hp => ⟨hKV0 hp,hKU hp⟩
  have hVPacket : V ⊆ packet.parameterDomain := inter_subset_left.trans hV0packet
  have hVO : V ⊆ Data.parameterOpen := inter_subset_right.trans hUO
  have hEach (nu : Fin Data.primaryCount) (a : Β) := round3_prepared_host_restrict_parameter
    (Data.atlas.chart (packet.piece nu a).host) (hd.atlas_smooth.chart_mem (packet.piece nu a).host)
    (b0 nu a) _ (e0 nu a) (hData0 nu a) V hV
  choose b e hData hSource hTarget hb hbi he hASource using hEach
  let host := fun nu a => (packet.piece nu a).host
  have hAllId (ip : Fin Data.parameterCount) : Data.parameterChart ip = OpenPartialHomeomorph.refl Ep := by
    have hip : ip = baseIndex.2 := Fin.ext (by have hi := ip.isLt; have hb := baseIndex.2.isLt; omega)
    rw [hip]
    exact hId
  have hActive (nu) (a : Β) (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source) :
      w ∈ Data.primaryDomain nu ∩ (V ×ˢ (univ : Set M)) := by
    rw [hASource] at hw
    have ha := hActive0 nu a w hw.1
    have hp : w ∈ Data.primaryDomain nu := by
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,Prod.mk.eta] using ha.1
    exact ⟨hp,hw.2⟩
  have hSupport (nu) (a : Β) : incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M))
      (packet.piece nu a).cutoff ⊆ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source := by
    intro w hw
    rw [hASource]
    refine ⟨hSupport0 nu a (parameterRound2_relativeSupport_mono_open
      (V0 ×ˢ (univ : Set M)) (V ×ˢ (univ : Set M)) (hV0.prod isOpen_univ) (hV.prod isOpen_univ)
      (fun _ hz => ⟨hz.1.1,hz.2⟩) _ hw),?_⟩
    rw [parameterRound2_global_relativeSupport_eq _ (hV.prod isOpen_univ)] at hw
    exact hw.1
  have hCover := round3_prepared_stable_primary_cover Data hd hs hn baseIndex hId packet
    V hV hVPacket b hSupport
    (by
      intro nu a w hw
      rw [hASource] at hw
      exact hActive0 nu a w hw.1)
  let domain := round3PreparedStablePrimaryDomain Data host b V
  let E := round3OriginalComputedPositiveData Data F H V rho
  let newStage : Round3RepairOriginalSmoothingStage E BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference Given :=
    stage.restrictParameter V
  let hdE := round3_computed_stage_domain Data hd F H V rho hV hKV hVO
  let hsE := round3_computed_stage_original_smooth_inputs Data hs F H V rho hVO
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference Given newStage
  have hFullSource (nu) (a : Β) :
      (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source ⊆
      (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (packet.piece nu a).native).source := by
    intro w hw
    exact ⟨hw.1,hSource0 nu a (hSource nu a hw.2)⟩
  refine ⟨V,hV,hKV,inter_subset_right,domain,?_⟩
  apply hMake E reference Given newStage hdE hsE hAllId baseIndex.2 domain
    (fun nu => (hCover nu).1) (fun nu _ hz => ((hCover nu).2.1 hz).1)
    (fun nu => (hCover nu).2.2.1) (fun _ => Β) host b e
  · intro nu a
    change ActualOriginalHostSliceData (Data.atlas.chart (packet.piece nu a).host)
      (b nu a) (Data.phase nu) (e nu a)
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,Prod.mk.eta] using hData nu a
  · exact hActive
  · intro nu a w hw
    exact packet.source_inner nu a w (hFullSource nu a hw)
  · exact fun nu => (hCover nu).2.2.2
  · intro nu a z hz w
    rw [he]
    exact hFirst0 nu a z (by rw [hTarget] at hz; exact hz.1) w
  · intro nu a z hz w
    rw [he]
    exact hFrame0 nu a z (by rw [hTarget] at hz; exact hz.1) w
  · intro nu a z hz
    have hh := hNormal0 nu a z (by rw [hTarget] at hz; exact hz.1)
    change (1/4 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
      (fderiv ℝ ((fun x => F (z.1,x)) ∘ (e nu a z.1).symm) z.2)
      (incrementsModeAmbientTransverseFrame (fun x => F (z.1,x)) (hF z.1) (e nu a z.1).symm z.2)
      (Data.freeNormal nu (z.1,(e nu a z.1).symm z.2))‖
    rw [he]
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hh
  · exact hGivenFinite
  · exact hGivenBound
  · intro nu a k z hz
    change ‖iteratedFDeriv ℝ k (b nu a).symm z‖ ≤ packet.Tchart k
    rw [hbi,hbi0]
    exact packet.chart_jets_target nu a k z (hTarget0 nu a (by rw [hTarget] at hz; exact hz.1))
  · intro nu a k z hz
    change ‖iteratedFDeriv ℝ k (b nu a) z‖ ≤ packet.Tforward k
    rw [hb,hb0]
    exact packet.forward_jets_source nu a k z (hSource0 nu a (hSource nu a hz))

#print axioms round3_exists_reference_C2_actual_normal_stage
end GlobalEmbedding.Continuation
