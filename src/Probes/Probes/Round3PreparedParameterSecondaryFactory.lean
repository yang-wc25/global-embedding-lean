import Probes.Round3PreparedParameterSecondaryC2
import Probes.Round3ParameterOriginalPrimarySamples

/-! The original RS/RP preparations internally supply all physical parents
and all true original parameter samples for the fixed signed-secondary
packet. No prepared secondary family is a caller premise. -/
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
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

 theorem round3_prepared_actual_original_parameter_secondary_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref) (hAll : Ref.parameterSet = univ)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Ref.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta,
      (∀ z, ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
      ∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2 := by
  intro theta
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hQT : ∀ i, Ref.parameterNormDomain i ⊆ (B.chart i).target := by
    rw [hChart]
    exact hd.parameter_norm_subset
  obtain ⟨W,hW,hKW,hSmooth,hCompact,hSupport,hPart,hCount⟩ :=
    round3Parameter_actual_compact_product_parents BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
      Ref.atlas B hd.atlas_smooth hB Ref.parameterSet RS RP Ref.sourceNormDomain Ref.parameterNormDomain
      hOmega hQ hd.source_norm_subset hQT hSource hParameter
  have hSmooth' (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :
      ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i) := by
    simpa only [modelWithCornersSelf_prod] using hSmooth i
  have hSampling := round3Parameter_product_parent_original_samples Ref B hChart BS0 TS0 BP0 TP0 Ds Dp RS RP hParameter
  have hSupport' (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :
      tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ Ref.atlas.inner i.1 :=
    fun z hz => ⟨(hSampling i z hz).1,(hSampling i z hz).2.1⟩
  obtain ⟨packet⟩ := round3_prepared_actual_parameter_secondary_pieces Ref hd hs hp hImm hAll theta
    hCompact hSmooth' hSupport'
  have hSupport'' (i : Fin Ref.atlas.count × Fin Ref.parameterCount) :
      tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSampling i z hz).1,mem_univ _⟩
  refine ⟨packet,(fun z => hPart z (hKW (by rw [hAll]; exact mem_univ _))),hCount,hSupport'',?_⟩
  intro r i a y hy
  have hNative := round3Parameter_native_compact_parent (Ref.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth' i) (hSupport'' i)
  have hCutoff : y ∈ tsupport (packet.piece r i a).cutoff :=
    ((packet.piece r i a).carrier_eq ▸ hy).1
  obtain ⟨z,hz,rfl⟩ := hNative.2.2 (packet.native_parent r i a hCutoff)
  exact (hSampling i z hz).2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_original_parameter_secondary_factory
