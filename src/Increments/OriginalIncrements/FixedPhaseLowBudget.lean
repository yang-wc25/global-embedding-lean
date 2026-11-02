import OriginalIncrements.OriginalLowBudgetLocalization
import OriginalIncrements.OriginalPhysicalPhaseJets

/-!
# Original phase-only low budgets manufacture the actual localization

Only the first two jets of the fixed original phase are bounded here, in
its literal original max-over-chart norm and evaluation domains. The input
contains no F/H derivative, raw cutoff, adapted chart, inverse, margin or
constructed estimate. The actual parameter neighborhood and localized raw
parents are manufactured by the existing continuity/cutoff construction.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology Classical
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
local notation "𝓙" => 𝓘(ℝ,D)

variable [CompactSpace M]


/-- A numerical phase-only profile; only entries zero and one are read. -/
def fixedOriginalPhaseProfile (Phase0 Phase1 : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then Phase0 else Phase1

theorem fixedOriginalPhaseProfile_nonneg (Phase0 Phase1 : ℝ)
    (h0 : 0 ≤ Phase0) (h1 : 0 ≤ Phase1) (k : ℕ) :
    0 ≤ fixedOriginalPhaseProfile Phase0 Phase1 k := by
  unfold fixedOriginalPhaseProfile
  split_ifs <;> assumption

/-- First and second original phase jets only, on the original norm domains.
Neither F/H nor any produced geometric object is read by this predicate. -/
def OriginalPhaseLowBounds
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (Phase0 Phase1 : ℝ) : Prop :=
  ∀ nu k, k ≤ 1 →
    paperAtlasWeighted 0 k 1 (actualOriginalTotalPhaseCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        ENNReal.ofReal (fixedOriginalPhaseProfile Phase0 Phase1 k)

theorem original_phase_only_positive_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hbudget0 : 0 ≤ budget) (nu : Fin Data.primaryCount)
    (hphase : paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        ENNReal.ofReal budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalPrimaryEvaluation Data nu i) :
    ell^k*‖iteratedFDeriv ℝ (k+1)
      (actualOriginalJointPhase Data nu i ∘ parameterTensorModelEquiv (m+1) d) z‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d j*budget := by
  let O := incrementsOriginalPrimaryDifferentiation Data nu
  let U := actualOriginalPhaseOpen Data nu
  let S := incrementsOriginalPrimaryEvaluation Data nu
  let f := actualOriginalTotalPhaseCoordinates Data nu
  let a := parameterTensorModelEquiv (m+1) d
  have hO (i) := actual_original_primaryDifferentiation_open Data hd.primary_open nu i
  have hU (i) := actualOriginalPhaseOpen_open Data hd nu i
  have hSU (i) := actualOriginalPhaseOpen_sample Data hd nu i
  have hf (i) := actualOriginalTotalPhaseCoordinates_contDiffOn Data hd hs nu i
  have hfin : paperAtlasWeighted 0 j ell f O S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hphase
  have hbound : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget := by
    simpa only [ENNReal.toReal_ofReal hbudget0] using
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hphase)
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  rw [he] at hfin hbound
  have hj := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f U S hU hSU hf hfin i hk
    (le_refl 0) hz
  simp only [Nat.add_zero] at hj
  have hcoef : ell^k*‖iteratedFDeriv ℝ k (f i) (a z)‖ ≤ coordinateDimensionFactor ((m+1)+d) j*budget :=
    hj.trans (mul_le_mul_of_nonneg_left hbound (coordinateDimensionFactor_nonneg _ _))
  have hDf : fderiv ℝ (actualOriginalJointPhase Data nu i) = actualScalarCovectorAssembly ((m+1)+d) ∘ f i := by
    funext y
    exact (actualScalarCovectorAssembly_exact ((m+1)+d) (fderiv ℝ (actualOriginalJointPhase Data nu i) y)).symm
  have hp := slow_linear_jet_bound (actualScalarCovectorAssembly ((m+1)+d)) (U i) (hU i) (f i) (hf i)
    k ell (coordinateDimensionFactor ((m+1)+d) j*budget) hell.le (a z) (hSU i hz) hcoef
  rw [← hDf,norm_iteratedFDeriv_fderiv] at hp
  have hpre := norm_iteratedFDeriv_comp_equiv_le a (actualOriginalJointPhase Data nu i) (k+1) z
  calc
    _ ≤ ell^k*(‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase Data nu i) (a z)‖*
        linearModelFactor a (k+1)) := mul_le_mul_of_nonneg_left hpre (pow_nonneg hell.le k)
    _ = linearModelFactor a (k+1)*(ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase Data nu i) (a z)‖) := by ring
    _ ≤ linearModelFactor a (j+1)*(‖actualScalarCovectorAssembly ((m+1)+d)‖*
        (coordinateDimensionFactor ((m+1)+d) j*budget)) :=
      mul_le_mul (linearModelFactor_mono a (by omega)) hp (by positivity) (linearModelFactor_nonneg _ _)
    _ = _ := by dsimp only [actualOriginalTotalPhaseJetCost,a]; ring

theorem original_phase_only_physical_sample_bound
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (k : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hBudget : 0 ≤ budget)
    (hPhase : paperAtlasWeighted 0 k ell (actualOriginalTotalPhaseCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        ENNReal.ofReal budget)
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
  have h := original_phase_only_positive_jets Data hd hs k ell budget hell
    hBudget nu hPhase i k le_rfl y hEval
  simpa only [originalPhaseJetAtPhysical,original_native_primary_phase_eq,y] using h

/-- Only the original finite two-entry budget is an input. The resulting
neighborhood is chosen once for all owner labels and phases, before every
later high derivative order and before the parameter localization. -/
theorem original_phase_only_parameter_neighborhood
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hPacket : ∀ k ≤ 1, 0 ≤ Packet k)
    (hPhase : ∀ nu k, k ≤ 1 →
      paperAtlasWeighted 0 k ell (actualOriginalTotalPhaseCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
          ENNReal.ofReal (Packet k)) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ V : Set P, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
        (k : ℕ), k ≤ 1 → ∀ z : P × M, z.1 ∈ V →
        z ∈ tsupport (theta i) → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
        originalPhaseJetAtPhysical Data nu i k ell z <
          actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
  intro theta
  let I := Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) × Fin 2
  let active : I → Set (P × M) := fun a => tsupport (theta a.2.1) ∩ tsupport (Data.cutoff a.1)
  let domain : I → Set (P × M) := fun a => originalPhasePhysicalDomain Data a.1 a.2.1
  let f : I → P × M → ℝ := fun a => originalPhaseJetAtPhysical Data a.1 a.2.1 a.2.2 ell
  let bound : I → ℝ := fun a => actualOriginalTotalPhaseJetCost (m+1) d a.2.2*Packet a.2.2
  have hRelative (nu : Fin Data.primaryCount) :
      incrementsOriginalRelativeCutoffSupport Data nu =
        incrementsOriginalParameterRegion Data ∩ tsupport (Data.cutoff nu) :=
    original_relative_cutoff_support_eq Data hd nu
  have hParent (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) :=
    original_raw_parent_own_samples Data B hChart BS TS BP TP Ds Dp RS RP hSource hParameter i z hz
  have hAD (a : I) :
      (Data.parameterOpen ×ˢ (univ : Set M)) ∩ active a ⊆ domain a := by
    intro z hz
    have hp := hParent a.2.1 z hz.2.1
    exact ⟨⟨hp.1,hp.2.1⟩,hd.cutoff_support_local a.1 ((hRelative a.1).symm ▸ ⟨hz.1,hz.2.2⟩),hz.1⟩
  have hD (a : I) : IsOpen (domain a) := original_phase_physical_domain_isOpen Data hd a.1 a.2.1
  have hCont (a : I) : ContinuousOn (f a) (domain a) :=
    original_phase_jet_physical_continuousOn Data hd hs a.1 a.2.1 a.2.2 ell
  have hBound (a : I) (z : P × M)
      (hz : z ∈ (Data.parameterSet ×ˢ (univ : Set M)) ∩ active a) : f a z ≤ bound a := by
    have hp := hParent a.2.1 z hz.2.1
    have hPrimary : z ∈ Data.primaryDomain a.1 := hd.cutoff_support_local a.1
      ((hRelative a.1).symm ▸ ⟨⟨hd.parameter_subset hz.1.1,hz.1.2⟩,hz.2.2⟩)
    exact original_phase_only_physical_sample_bound Data hd hs a.1 a.2.1 a.2.2
      ell (Packet a.2.2) hell (hPacket a.2.2 (by omega)) (hPhase a.1 a.2.2 (by omega)) z
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hz.1.1 hPrimary
  obtain ⟨V,hV,hKV,hVU,hVbound⟩ := finite_active_inputs_parameter_neighborhood
    Data.parameterSet Data.parameterOpen hd.parameter_open hd.parameter_subset active domain
    (fun _ => (isClosed_tsupport _).inter (isClosed_tsupport _)) hD hAD f bound hCont hBound 1 zero_lt_one
  refine ⟨V,hV,hKV,hVU,?_⟩
  intro nu i k hk z hz htheta hcutoff
  have h := hVbound (nu,i,⟨k,by omega⟩) z
    ⟨⟨hz,mem_univ _⟩,htheta,((hRelative nu) ▸ hcutoff).2⟩
  exact h

theorem original_parameter_localization_with_phase_only_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hPacket : ∀ k ≤ 1, 0 ≤ Packet k)
    (hPhase : ∀ nu k, k ≤ 1 →
      paperAtlasWeighted 0 k ell (actualOriginalTotalPhaseCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
          ENNReal.ofReal (Packet k)) :
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      EqOn psi 1 V ∧
      let theta := fun i => sourceCollarNovParameterLocalized psi
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ i, IsCompact (tsupport (theta i))) ∧
      (∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
        (k : ℕ), k ≤ 1 → ∀ z : P × M,
        z ∈ tsupport (theta i) → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
        originalPhaseJetAtPhysical Data nu i k ell z <
          actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
  obtain ⟨W,hW,hKW,hWU,hLow⟩ := original_phase_only_parameter_neighborhood Data hd hs
    B hChart BS TS BP TP Ds Dp RS RP hSource hParameter ell hell Packet hPacket hPhase
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  obtain ⟨psi,V,hV,hKV,hVW,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,hPart,hCount,hGerm⟩ :=
    completion_original_parameter_localized_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet W hd.parameter_compact hW hKW RS RP
  refine ⟨psi,V,hV,hKV,hVW.trans hWU,hOne,hSmooth,hCompact,?_,hPart,hCount,?_⟩
  · intro i z hz
    have hi := hSupport i hz
    exact ⟨⟨by simpa only [hChart] using hi.1.1,hWU hi.1.2⟩,hi.2⟩
  · intro nu i k hk z hz hcutoff
    exact hLow nu i k hk z (hSupport i hz).1.2
      (sourceCollarNov_parameter_localized_tsupport psi _ hz).1 hcutoff

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_phase_only_positive_jets
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_parameter_localization_with_phase_only_budget
