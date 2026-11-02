import Repair.FullIncrementNovOpenPrimaryPieces
import Smoothing.Round3ParameterCompactParents

/-! Original-input primary factory on a genuine neighborhood of the compact
parameter set.  It uses the original source and parameter buffered raw
preparations and their original sampling domains.  The actual raw parameter
cutoffs are supported in the original parameter-open set.  No all-parameter hypothesis,
new decomposition, new free normals or output estimate is requested.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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

theorem fullIncrementNov_original_open_primary_factory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP0 TP0 Dp)
    (hRawOpen : ∀ i, tsupport (RP.raw i) ⊆ Data.parameterOpen)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ (V : Set P), IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ i, tsupport (theta i) ⊆ ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      Nonempty (Round3ParameterWholePrimaryPieceSupply Data theta) := by
  intro theta
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hQT : ∀ i, Data.parameterNormDomain i ⊆ (B.chart i).target := by
    rw [hChart]
    exact hd.parameter_norm_subset
  obtain ⟨V,hV,hKV,hSmooth,hCompact,hSupport,hPart,hCount⟩ :=
    round3Parameter_actual_compact_product_parents BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet RS RP Data.sourceNormDomain Data.parameterNormDomain
      hOmega hQ hd.source_norm_subset hQT hSource hParameter
  have hSmooth' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i) := by
    simpa only [modelWithCornersSelf_prod] using hSmooth i
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1 := by
    intro z hz
    have hh := hSupport i hz
    have hParam : z.1 ∈ tsupport (RP.raw i.2) :=
      tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2
        ((parameterLocalProductCutoff_tsupport_subset Data.atlas B
          (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw) i
          (round3ParameterProductParent_tsupport Data.atlas B _ _ i hz)).1)
    refine ⟨⟨?_,hRawOpen i.2 hParam⟩,hh.2⟩
    rw [← hChart]
    exact B.inner_subset i.2 hh.1
  exact ⟨V ∩ Data.parameterOpen,hV.inter hd.parameter_open,
    fun p hp => ⟨hKV hp,hd.parameter_subset hp⟩,inter_subset_right,
    fun z hz => hPart z hz.1,hCount,hSupport',
    fullIncrementNov_original_open_primary_pieces Data hd hs hp theta hCompact hSmooth' hSupport'⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_primary_factory
