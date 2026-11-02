import OriginalIncrements.SampledSecondaryObserverProfiles

/-! Actual signed-secondary profiles at the current original input scale.
The positive profiles depend only on the original Given envelope and low
mu/Mb; the literal localized cutoff retains its original raw profile. -/
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

theorem original_sampled_secondary_profiles_at_scale
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V)
    (hKV : Data.parameterSet ⊆ V) (hOne : EqOn psi 1 V) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
      (controls : ∀ r i a, ActualPhaseSampleJetControls mu Mb
        ((actualOriginalParameterSignedPhase Data i r.val) ∘
          (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm)
        (packet.piece r i a).native)
      (hLiteral : ∀ r i a, (packet.piece r i a).cutoff = actualHostRefinementCutoff
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1))
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
        (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val))
      (hScalar : ∀ r i j (a : packet.s r i) x,
        buffer^j*‖iteratedFDeriv ℝ j
          (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
            (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j)
      (Parameter Spatial Packet : ℕ → ℝ)
      (hParameterNonneg : ∀ j, 0 ≤ Parameter j) (hSpatialNonneg : ∀ j, 0 ≤ Spatial j)
      (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
      (ell : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
      (hFinite : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
      (hBudget : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j),
      IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta packet ell
        (phaseObserverInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial)
        (incrementSecondaryCutoffProfile X mu Mb buffer BS TS BP TP Ds Dp)
        (phaseObserverForwardBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial) := by
  intro theta packet controls hLiteral hScalar Parameter Spatial Packet hPN hSN transition
    ell hell hellOne hFinite hBudget
  have hSupport (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1 := by
    intro z hz
    have hi := CollarCompletion.original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hz
    refine ⟨?_,hi.2⟩
    simpa only [hChart] using B.inner_subset i.2 hi.1
  have hSamples := localized_parent_original_carrier_samples Data B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter psi
  exact {
    positive := original_sampled_secondary_positive_profiles Data hd hs theta packet mu Mb hmu hMb
      controls hSupport hSamples Parameter Spatial Packet hPN hSN transition ell hell hellOne hFinite hBudget
    cutoff := localized_source_sample_secondary_cutoff_profiles Data hd hs mu Mb buffer hmu hMb hbuffer
      BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP psi V hV hKV hOne
      packet hLiteral hScalar ell hell.le hellOne }

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_sampled_secondary_profiles_at_scale
