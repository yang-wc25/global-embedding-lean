import Probes.Round3ParameterWholePieceReplacement
import Smoothing.Round4WholePrimaryPieceProfiles
import Probes.Round3ParameterWholePrimaryFactory

/-! Concrete reference factory for the original whole-parameter repair
caller. The SAME source/parameter preparation produces the global partition,
all phase-adapted pieces WITH their exact original-input derivative producers,
positive conditioning, every fixed chart profile,
and one C2 entrance tolerance. No primary family, chart profile, stable new
frame or parameter-neighborhood choice is supplied by the caller. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round4Parameter_actual_original_reference_factory_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hAll : Ref.parameterSet = univ)
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
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta),
      (∀ nu i, Nonempty (Round4PrimaryJetSupply Ref i nu
        ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
        (packet.s nu i) (packet.piece nu i))) ∧
    ∃ profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet,
      Round3ParameterOriginalPrimaryGeometry Ref
        (round3ParameterWholePrimaryFamily Ref hd hs hn theta
          (packet.replacePieces Ref theta profiles.piece profiles.host profiles.cutoff))
        (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) ∧
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
      Nonempty (Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) := by
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
  obtain ⟨packet,hPacketJets⟩ := round4Parameter_actual_whole_primary_pieces_profiles Ref hd hs hp hAll theta
    hCompact hSmooth' hSupport'
  have hCarriers := round3Parameter_whole_primary_original_carriers Ref hd theta packet hCompact hSmooth' hSampling
  obtain ⟨profiles⟩ := round3Parameter_actual_whole_reference_profiles Ref hd hs hp hImm hF0joint hAll
    theta packet (fun nu i a y hy => (hCarriers nu i a y hy).1)
  refine ⟨packet,hPacketJets,profiles,?_,?_⟩
  · apply round3Parameter_whole_primary_family_geometry Ref hd hs hn theta
      (packet.replacePieces Ref theta profiles.piece profiles.host profiles.cutoff)
      (fun z => hPart z (hKW (by rw [hAll]; exact mem_univ _))) _ hCount
  · exact round3Parameter_whole_reference_stable_family Ref hd hs hn hF0joint hAll theta packet profiles
      (fun nu i a y hy => (hCarriers nu i a y hy).2)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_actual_original_reference_factory_profiles
