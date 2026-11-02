import Probes.Round3ParameterOriginalPrimaryGeometry
import Smoothing.Round3RepairOriginalSmoothingStageData

/-! A genuine all-parameter primary-family factory from the SAME raw source
and parameter preparation used by the original smoother. The physical parent
is literally chi_source^2*chi_parameter^2. On K=P it is a global partition;
the all-chart primary family is selected once, before any solver order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)
local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

set_option backward.isDefEq.respectTransparency true in
theorem round3Parameter_actual_whole_primary_factory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (RS : TensorRawCutoffPreparation Data.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP0 TP0 Dp)
    (Omega : Fin Data.atlas.count → Set D) (Q : Fin Data.parameterCount → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOT : ∀ i, Omega i ⊆ (Data.atlas.chart i).target) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      Round3ParameterOriginalPrimaryGeometry Data (round3ParameterWholePrimaryFamily Data hd hs hn theta packet)
        (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) := by
  intro theta
  obtain ⟨W,hW,hKW,hSmooth,hCompact,hSupport,hPart,hCount⟩ :=
    round3Parameter_actual_compact_product_parents BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet RS RP Omega Q hOmega hQ hOT hQT hSource hParameter
  have hSmooth' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i) := by
    simpa only [modelWithCornersSelf_prod] using hSmooth i
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1 := by
    intro z hz
    have hh := hSupport i hz
    exact ⟨by rw [← hChart]; exact B.inner_subset i.2 hh.1,hh.2⟩
  obtain ⟨packet⟩ := round3Parameter_actual_whole_primary_pieces Data hd hs hp hAll theta
    hCompact hSmooth' hSupport'
  refine ⟨packet,round3Parameter_whole_primary_family_geometry Data hd hs hn theta packet ?_ _ hCount⟩
  intro z
  exact hPart z (hKW (by rw [hAll]; exact mem_univ _))

set_option backward.isDefEq.respectTransparency true in
theorem round3Parameter_actual_smoothed_whole_primary_factory
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ) :
    let theta := round3ParameterProductParent Data.atlas stage.parameterFamily
      (squareNormalizedCutoff stage.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff stage.parameterPreparation.raw)
    ∃ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      Round3ParameterOriginalPrimaryGeometry Data (round3ParameterWholePrimaryFamily Data hd hs hn theta packet)
        (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) := by
  exact round3Parameter_actual_whole_primary_factory Data hd hs hp hn hAll BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp stage.parameterFamily stage.chart_eq stage.parameter_smooth
    stage.sourcePreparation stage.parameterPreparation stage.Omega stage.Q
    stage.source_compact stage.parameter_compact stage.source_target stage.parameter_target
    stage.source_sampling stage.parameter_sampling

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_whole_primary_factory
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_smoothed_whole_primary_factory
