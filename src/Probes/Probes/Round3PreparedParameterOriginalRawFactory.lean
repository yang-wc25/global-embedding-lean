import Probes.Round3PreparedParameterActualRawPieces
import Probes.Round3PreparedParameterOriginalStableSecondaryFactory
import Probes.Round3PreparedParameterSecondaryStablePartition
import Smoothing.ParameterRound2CompactNorms

/-! Original buffered source/parameter preparations produce the whole
coherent secondary raw factory. The reference packet, all derivative costs
and the C2 threshold are fixed before SF. The current map supplies no new
geometry or cutoff budgets. Every actual native choice is the canonical
pullback of the one physical stable family. -/
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

 theorem round3_prepared_actual_original_parameter_raw_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref) (hAll : Ref.parameterSet = univ)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
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
      ∃ Tinv Kcut Tobs : ℕ → ℝ, ∃ epsilon : ℝ,
        (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Kcut k) ∧ (∀ k, 0 ≤ Tobs k) ∧ 0 < epsilon ∧
      ∀ (F : P → M → Ey)
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
      ∃ stable : ∀ r i (a : packet.s r i),
        Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF,
      (∀ (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) z,
        z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2) →
        GoodCovector (F z.1) (hF z.1) z.2
          ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
            (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2))) ∧
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
        (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
        (domain : Fin Ref.primaryCount → Set (P × M))
        (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
      let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
      ∀ (hdNew : IncrementsOriginalDomainConditions Data) (hsNew : IncrementsOriginalSmoothInputs Data),
      IncrementsOriginalSliceImmersionInputs Data →
      ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      ∃ out : Round3PreparedParameterRawPiece Data hdNew hsNew (i.1,observer) r
        ((Ref.parameterChart observer).target ×ˢ (univ : Set M))
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,observer)),
        out.choice = (choice.pullback (Ref.parameterChart observer)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (packet.piece r i a).cT/16 ∧ out.Bnative = 1+Tobs 1 := by
  intro theta
  obtain ⟨packet,hPart,hCount,hSupport,hParam⟩ :=
    round3_prepared_actual_original_parameter_secondary_factory Ref hd hs hp hImm hAll
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  obtain ⟨epsS,hepsS,hStable⟩ := round3_prepared_parameter_secondary_stable_family Ref hd hs hAll
    theta packet hParam hF0joint
  obtain ⟨epsG,hepsG,hGood⟩ := round3_prepared_parameter_packet_signed_good Ref hd hs hAll
    theta packet hPart hSupport hParam hF0joint
  have hCompact (i) : IsCompact (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i) := by
    rw [hAll]
    exact parameterRound2_originalEvaluation_univ_compact Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain hOmega hQ hd.source_norm_subset hd.parameter_norm_subset i
  obtain ⟨Ti,Tc,Tf,hTi,hTc,hTf,hRaw⟩ :=
    round3_prepared_actual_parameter_raw_pieces Ref hd hs hAll theta packet hSupport hCompact
  refine ⟨packet,hPart,hCount,hSupport,Ti,Tc,Tf,min epsS epsG,hTi,hTc,hTf,lt_min hepsS hepsG,?_⟩
  intro F hFjoint hF S hFinite hBound
  obtain ⟨stable⟩ := hStable F hFjoint hF hFinite (hBound.trans (min_le_left _ _))
  exact ⟨stable,hGood F hFjoint hF hFinite (hBound.trans (min_le_right _ _)),hRaw F hF stable⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_original_parameter_raw_factory
