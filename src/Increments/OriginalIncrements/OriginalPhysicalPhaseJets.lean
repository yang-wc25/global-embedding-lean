import Probes.Round3PreparedOriginalDomains
import CollarCompletion.OriginalParentSampling

/-! Literal physical-point evaluation of the original native phase jets. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

def originalNativePrimaryPhase
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) : X → ℝ :=
  fun y => Data.phase nu ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm y.2)

def originalPhasePhysicalDomain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) : Set (P × M) :=
  ((Data.parameterChart i.2).source ×ˢ (Data.atlas.chart i.1).source) ∩
    (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)

/-- Literal mixed phase jets at the actual point in its owner chart. -/
def originalPhaseJetAtPhysical
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (k : ℕ) (ell : ℝ) (z : P × M) : ℝ :=
  ell^k*‖iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i)
    ((Data.parameterChart i.2) z.1,(Data.atlas.chart i.1) z.2)‖

omit [BoundarylessManifold 𝓘(ℝ,D) M] [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem original_relative_cutoff_support_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (nu : Fin Data.primaryCount) :
    incrementsOriginalRelativeCutoffSupport Data nu =
      incrementsOriginalParameterRegion Data ∩ tsupport (Data.cutoff nu) := by
  let W := incrementsOriginalParameterRegion Data
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  change Subtype.val '' closure (Subtype.val ⁻¹' Function.support (Data.cutoff nu) : Set W) =
    W ∩ closure (Function.support (Data.cutoff nu))
  rw [← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Function.support (Data.cutoff nu)),Set.image_preimage_eq_inter_range]
  simp only [Subtype.range_coe_subtype,Set.ofPred_mem_eq,Set.inter_comm]

theorem original_native_primary_phase_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d =
      originalNativePrimaryPhase Data nu i := by
  funext y
  exact congrArg (Data.phase nu) (actual_original_jointPoint_native Data i y)

omit [BoundarylessManifold 𝓘(ℝ,D) M] [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem original_phase_physical_domain_isOpen
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    IsOpen (originalPhasePhysicalDomain Data nu i) :=
  ((Data.parameterChart i.2).open_source.prod (Data.atlas.chart i.1).open_source).inter
    ((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ))

theorem original_phase_physical_chart_maps
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    MapsTo (fun z : P × M => ((Data.parameterChart i.2) z.1,(Data.atlas.chart i.1) z.2))
      (originalPhasePhysicalDomain Data nu i) (actualOriginalPrimaryNativeOpen Data nu i) := by
  intro z hz
  apply round3_prepared_native_primary_mem Data i nu _
    ((Data.atlas.chart i.1).map_source hz.1.2) ((Data.parameterChart i.2).map_source hz.1.1)
  simpa only [(Data.parameterChart i.2).left_inv hz.1.1,(Data.atlas.chart i.1).left_inv hz.1.2] using hz.2

theorem original_phase_jet_physical_continuousOn
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (k : ℕ) (ell : ℝ) :
    ContinuousOn (originalPhaseJetAtPhysical Data nu i k ell) (originalPhasePhysicalDomain Data nu i) := by
  let U := actualOriginalPrimaryNativeOpen Data nu i
  have hU : IsOpen U := actualOriginalPrimaryNativeOpen_isOpen Data hd nu i
  have hpsi : ContDiffOn ℝ ∞ (originalNativePrimaryPhase Data nu i) U :=
    round3_actual_original_primary_native_phase_smooth Data hd hs nu i
  have hJet : ContinuousOn (iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i)) U := by
    apply (hpsi.continuousOn_iteratedFDerivWithin (m := k+1) (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hU hx).symm
  have hq : ContinuousOn
      (fun z : P × M => ((Data.parameterChart i.2) z.1,(Data.atlas.chart i.1) z.2))
      (originalPhasePhysicalDomain Data nu i) :=
    ((Data.parameterChart i.2).continuousOn.comp continuous_fst.continuousOn
      (fun _ hz => hz.1.1)).prodMk
    ((Data.atlas.chart i.1).continuousOn.comp continuous_snd.continuousOn
      (fun _ hz => hz.1.2))
  exact continuousOn_const.mul ((hJet.comp hq (original_phase_physical_chart_maps Data nu i)).norm)

theorem original_phase_jet_physical_original_sample_bound
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (k : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hFinite : actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : (actualOriginalGivenInputProfile Data k ell).toReal ≤ budget)
    (z : P × M) (hParam : z.1 ∈ (Data.parameterChart i.2).source)
    (hSource : z.2 ∈ (Data.atlas.chart i.1).source)
    (hQ : Data.parameterChart i.2 z.1 ∈ Data.parameterNormDomain i.2)
    (hOmega : Data.atlas.chart i.1 z.2 ∈ Data.sourceNormDomain i.1)
    (hK : z.1 ∈ Data.parameterSet) (hPrimary : z ∈ Data.primaryDomain nu) :
    originalPhaseJetAtPhysical Data nu i k ell z ≤ actualOriginalTotalPhaseJetCost (m+1) d k*budget := by
  let y : X := ((Data.parameterChart i.2) z.1,(Data.atlas.chart i.1) z.2)
  have hEval : parameterTensorModelEquiv (m+1) d y ∈ incrementsOriginalPrimaryEvaluation Data nu i := by
    refine ⟨(actual_original_native_evaluation_iff Data hd i y).mpr ?_,?_⟩
    · exact ⟨hOmega,hQ,by simpa only [y,(Data.parameterChart i.2).left_inv hParam] using hK⟩
    · change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
        (parameterTensorModelEquiv (m+1) d y) ∈ Data.primaryDomain nu
      rw [actual_original_jointPoint_native]
      simpa only [y,(Data.parameterChart i.2).left_inv hParam,(Data.atlas.chart i.1).left_inv hSource] using hPrimary
  have h := actual_original_given_phase_positive_jets Data hd hs k ell budget hell
    hFinite hBudget nu i k le_rfl y hEval
  simpa only [originalPhaseJetAtPhysical,original_native_primary_phase_eq,y] using h

omit [BoundarylessManifold 𝓘(ℝ,D) M] in
theorem original_raw_parent_own_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
    (hz : z ∈ tsupport (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)) :
    z.1 ∈ (Data.parameterChart i.2).source ∧ z.2 ∈ (Data.atlas.chart i.1).source ∧
      Data.parameterChart i.2 z.1 ∈ Data.parameterNormDomain i.2 ∧
      Data.atlas.chart i.1 z.2 ∈ Data.sourceNormDomain i.1 := by
  let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw) i
  have hEq : sourceCollarNovParameterLocalized (fun _ : P => 1) theta = theta := by
    funext z
    exact one_mul _
  have hlocal : z ∈ tsupport (sourceCollarNovParameterLocalized (fun _ : P => 1) theta) := by
    rw [hEq]
    exact hz
  have h := original_parameter_localized_parent_own_samples Data.atlas B Data.parameterSet
    BS TS BP TP Ds Dp RS RP Data.sourceNormDomain Data.parameterNormDomain hSource hParameter
    (fun _ => 1) i z hlocal
  simpa only [hChart] using h

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_phase_jet_physical_original_sample_bound
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_raw_parent_own_samples
