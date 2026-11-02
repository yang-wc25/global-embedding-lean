import Smoothing.Round3RepairParameterStablePhase
import Probes.Round3ParameterOriginalReferenceFactory
import Probes.Round3PreparedParameterOriginalSignedGood

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
local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

/-- Original RS/RP data choose one whole-parameter phase tolerance before
any perturbing map. All primary, doubled and signed phase conditions are
then obtained on a genuine common carrier for that same map. -/
theorem round3_repair_original_parameter_phase_factory
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
    ∃ domain : Fin Ref.primaryCount → Set (P × M),
      (∀ nu, domain nu ⊆ Ref.primaryDomain nu) ∧
      (∀ nu, tsupport (Ref.cutoff nu) ⊆ domain nu) ∧
      let E : IncrementsOriginalNativeData (m+1) d N M P :=
        {Ref with F := Function.uncurry F, primaryDomain := domain}
      ∃ hdE : IncrementsOriginalDomainConditions E,
      ∃ hsE : IncrementsOriginalSmoothInputs E,
        IncrementsOriginalPhaseConditions E hdE hsE := by
  obtain ⟨packet,profiles,hGeometry,epsilonP,hEpsilonP,hStable⟩ :=
    round3Parameter_actual_original_reference_factory Ref hd hs hp hn hImm hF0joint hAll
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  obtain ⟨epsilonS,hEpsilonS,hSigned⟩ :=
    round3_prepared_actual_original_parameter_signed_good Ref hd hs hp hImm hAll hF0joint
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
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
  refine ⟨min epsilonP epsilonS,lt_min hEpsilonP hEpsilonS,?_⟩
  intro F hFjoint hF S hFinite hSmall
  obtain ⟨stable⟩ := hStable F hFjoint hF hFinite (hSmall.trans (min_le_left _ _))
  exact round3_repair_parameter_stable_full_phase Ref hd hs hn hAll _ packet profiles _
    (fun z => hPart z (hKW (by rw [hAll]; exact mem_univ _))) hCount F hFjoint hF stable
    (hSigned F hFjoint hF hFinite (hSmall.trans (min_le_right _ _)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_original_parameter_phase_factory
