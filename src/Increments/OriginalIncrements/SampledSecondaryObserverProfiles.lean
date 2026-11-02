import OriginalIncrements.SampledSignedNativeJets
import OriginalIncrements.CarrierSampleSecondaryProfiles
import CompletionIntegration.PointwiseObserverJets
import IncrementsCompletion.AtScaleSecondaryPacketProfiles

/-! The same actual signed packet is observed only at unchanged original
samples. All positive chart jets use the current original Given envelope;
no high-order bound on the open construction region enters these profiles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem original_secondary_carrier_native_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1)
    (hSamples : ∀ i z, z ∈ tsupport (theta i) →
      (Data.parameterChart i.2) z.1 ∈ Data.parameterNormDomain i.2 ∧
      (Data.atlas.chart i.1) z.2 ∈ Data.sourceNormDomain i.1)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : packet.s r i)
    (observer : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hz : parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer)
    (hCarrier : ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
      round3PreparedParameterSecondaryCarrier Data r
        (round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a))) :
    let point := incrementsCompletionOriginalHostPoint Data i.2 i.1 observer z
    point ∈ (packet.piece r i a).native.source ∧
      parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data r.val.1.1 i ∧
      parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data r.val.1.2 i := by
  intro point
  let physical : P × M := ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2)
  let piece := packet.piece r i a
  have hParent : physical ∈ tsupport (theta i) := packet.parent r i a hCarrier.1
  have hp : physical.1 ∈ (Data.parameterChart i.2).source := (hSupport i hParent).1
  have hx : physical.2 ∈ (Data.atlas.chart i.1).source := Data.atlas.inner_subset i.1 (hSupport i hParent).2
  have hOwn := hSamples i physical hParent
  have hNative := (round3_prepared_parameter_secondary_carrier_source Data hd hs i r piece (theta i)
    (fun y hy => ⟨(hSupport i hy).1,mem_univ _⟩) (packet.parent r i a)).2 hCarrier
  have hAdapted := piece.carrier_source hNative
  have hPoint : point ∈ piece.native.source := hAdapted.2
  have hEval := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hOwnEval : parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalEvaluation Data.atlas
      Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i := by
    apply (actual_original_native_evaluation_iff Data hd i point).mpr
    refine ⟨hOwn.2,hOwn.1,?_⟩
    change (Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1) ∈ Data.parameterSet
    rw [(Data.parameterChart i.2).left_inv hp]
    exact hEval.2.2
  have hActive : physical ∈ Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      physical ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data := by
    have h := piece.active _ hAdapted
    change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1),physical.2) ∈ _ ∧
      ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1),physical.2) ∈ _ at h
    simpa only [(Data.parameterChart i.2).left_inv hp,Prod.eta] using h
  have hSample (nu : Fin Data.primaryCount) (hn : physical ∈ Data.primaryDomain nu) :
      parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data nu i := by
    refine ⟨hOwnEval,?_⟩
    change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterTensorModelEquiv (m+1) d point) ∈ Data.primaryDomain nu
    rw [actual_original_jointPoint_native]
    change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1),
      (Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) physical.2)) ∈ Data.primaryDomain nu
    rw [(Data.parameterChart i.2).left_inv hp,(Data.atlas.chart i.1).left_inv hx]
    exact hn
  exact ⟨hPoint,hSample _ hActive.1.1,hSample _ hActive.2.1⟩

theorem original_sampled_secondary_positive_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (mu Mb : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (controls : ∀ r i a, ActualPhaseSampleJetControls mu Mb
      ((actualOriginalParameterSignedPhase Data i r.val) ∘
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm)
      (packet.piece r i a).native)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1)
    (hSamples : ∀ i z, z ∈ tsupport (theta i) →
      (Data.parameterChart i.2) z.1 ∈ Data.parameterNormDomain i.2 ∧
      (Data.atlas.chart i.1) z.2 ∈ Data.sourceNormDomain i.1)
    (Parameter Spatial Packet : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (ell : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hBudget : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j) :
    ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤
          phaseObserverForwardBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤
          phaseObserverInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial k := by
  intro r i a observer k hk choice native t z hz hCarrier
  let piece := packet.piece r i a
  have hPreserves : Round3ParameterChartPreserves piece.native :=
    (round3_prepared_signed_native_preserves_phase Data hd hs i r _ piece).1
  let b := round3ParameterCrossNativeChart (Data.parameterChart i.2)
    (Data.parameterChart observer.2) piece.native
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
      (Data.parameterChart observer.2) (Data.atlas.chart i.1) piece.native hPreserves).symm
  have hEval := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hp : z.1 ∈ (Data.parameterChart observer.2).target := hd.parameter_norm_subset observer.2 hEval.2.1
  have hx : z.2 ∈ (Data.atlas.chart observer.1).target := hd.source_norm_subset observer.1 hEval.1
  have hSource : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Data.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Data hd hs i r _ piece)
      (z.1,(Data.atlas.chart observer.1).symm z.2) hp).mpr
    exact packet.source r i a hCarrier
  have hOwn := hSamples i
    ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2)
    (packet.parent r i a hCarrier.1)
  have hPoint := original_secondary_carrier_native_samples Data hd hs theta packet hSupport hSamples
    r i a observer z hz hCarrier
  let point := incrementsCompletionOriginalHostPoint Data i.2 i.1 observer z
  let Phase := signedPhaseFromGivenBudget m d Packet
  have hNative := original_signed_native_positive_jets_at Data hd hs i r mu Mb hmu hMb piece.native
    (controls r i a) point hPoint.1 hPoint.2.1 hPoint.2.2 Packet ell hell k
    (fun j _ => hFinite j) (fun j _ => hBudget j)
  have hJets := incrementsCompletion_original_native_observer_finite_weighted_jets_at
    Data hd i.2 i.1 piece.native (actualOriginalParameterSignedPhase Data i r.val)
    piece.slices piece.data hPreserves (phaseForwardBudget Mb Phase) (phaseInverseBudget mu Mb Phase)
    Parameter Spatial
    (fun j _ => phaseForwardBudget_nonneg Mb hMb Phase (fun j _ => signedPhaseFromGivenBudget_nonneg m d Packet j) j)
    (fun j _ => phaseInverseBudget_nonneg mu Mb hmu hMb Phase (fun j _ => signedPhaseFromGivenBudget_nonneg m d Packet j) j)
    (fun j _ => hParameter j) (fun j _ => hSpatial j) transition
    ell hell hellOne observer z hEval.2.1 hEval.1 hOwn.1 hOwn.2 k hk
    (fun j hj hjk => (hNative j hj hjk).1) (fun j hj hjk => (hNative j hj hjk).2)
  have ht : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
      (actualHostAdaptedChart (Data.atlas.chart i.1) b) := by
    dsimp only [t]
    rw [hChart]
  have hAt := hJets (ht ▸ hSource)
  rw [← ht] at hAt
  exact hAt

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_secondary_carrier_native_samples
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_sampled_secondary_positive_profiles
