import Smoothing.Round3OuterActualLocalTargetControl
import Smoothing.Round3OuterLocalPositiveCone

/-! A direct repair consumer: the same literal map/tensor smoother supplies
original C2 map control, original C0 target control, and the computed target's
whole qualitative positive decomposition record on a neighborhood of K.
The reference packet is fixed before the new map, tensor and smoothing scale.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold MeasureTheory
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local instance computedPositiveChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance computedPositiveIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

def round3OriginalComputedPositiveData
    (D : IncrementsOriginalNativeData n d N M P) (SF : P × M → Ey)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (U : Set P) (reserve : ℝ) : IncrementsOriginalNativeData n d N M P :=
  { round3OriginalLocalRetargetPositiveConeData D T U reserve with F := SF }

/-- The numerical smallness is on the original old defect and the actual
smoothing tail. Target symmetry, target smoothness, target membership,
decomposition and positive reserve are all derived, not supplied. -/
theorem round3Outer_exists_uniform_computed_positive_target
    (BS0 TS BP0 TP : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Data : IncrementsOriginalNativeData n d N M P)
      (hd : IncrementsOriginalDomainConditions Data)
      (hLinear : IncrementsOriginalLinearSmoothInputs Data)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
      (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
      (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
      (hChart : B.chart = Data.parameterChart)
      (RS : TensorRawCutoffPreparation Data.atlas BS0 TS Ds)
      (RP : TensorLocalRawPreparation B Data.parameterSet BP0 TP Dp),
    radius ≤ min B.buffer Data.atlas.buffer →
    ∀ (Omega : Fin Data.atlas.count → Set Es) (Q : Fin Data.parameterCount → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (Data.atlas.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Omega i) →
    (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    (∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)) →
    ∀ ell t : ℝ, 0 < ell → ell ≤ t → t ≤ 1 →
    ∀ (u : P × M → Ey),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas B.chart u i)
      (incrementsOriginalDifferentiation Data.atlas B.chart i)) →
    ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas B.chart H i)
      (incrementsOriginalDifferentiation Data.atlas B.chart i)) →
    (∀ p x, (H p x).IsSymm) →
    ∀ (F0 : P × M → Ey), ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F0 →
    Data.H = (fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x) →
    Data.reference = Data.H →
    ∀ a inherited reference budget ML : ℝ, 0 ≤ a →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
      (fun p x => H p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ inherited →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ reference →
    (parameterLocalOriginalTotalPairWeighted Data.atlas B u H r t
      (incrementsOriginalEvaluation Data.atlas B.chart Omega Q univ)).toReal ≤ budget →
    incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ →
    (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML →
    ‖actualOriginalCoefficientFunctional n‖ * ML *
      (C*budget*(ell/t)^r+inherited+a*reference) ≤ rho/2 →
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu radius hradius r
    let chi := parameterLocalProductCutoff Data.atlas B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily Data.atlas B) mu K ell chi u
    let SH := tensorLocalParameterSmoothing Data.atlas B hd.atlas_smooth mu K ell chi H
    let Target := fun p x => SH p x-a • Data.H p x
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ SF ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => u z-SF z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S ≠ ⊤ ∧
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => u z-SF z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S).toReal ≤ C*budget*(ell/t)^r ∧
    ∃ U : Set P, IsOpen U ∧ Data.parameterSet ⊆ U ∧ U ⊆ Data.parameterOpen ∧
      IncrementsOriginalDomainConditions (round3OriginalComputedPositiveData Data SF Target U (rho/4)) ∧
      IncrementsOriginalQualitativeDecompositionInputs
        (round3OriginalComputedPositiveData Data SF Target U (rho/4)) ∧
      IncrementsOriginalDecompositionReserveInputs
        (round3OriginalComputedPositiveData Data SF Target U (rho/4)) (rho/4) := by
  obtain ⟨C,hC,hControl⟩ := round3Outer_exists_uniform_actual_local_target_low_control
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS BP0 TP hBS0 hTS hBP0 hTP Ds Dp radius hradius r
  refine ⟨C,hC,?_⟩
  intro Data hd hLinear hDecomp rho hReserve B hChart RS RP hbuffer Omega Q hOmega hQ
    hOT hQT hsource hparameter hScompact ell t hell helt ht1 u hu H hH hHs F0 hF0 hH0 hRef
    a inherited reference budget ML ha S hInherited hReference hBudget hProfile hML hSmall
    mu K chi SF SH Target
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hS : ∀ i, S i ⊆ round3OuterOriginalEvaluation Data.atlas B Data.parameterSet i := by
    intro i y hy
    change y ∈ round3OuterOriginalEvaluation Data.atlas B Data.parameterSet i
    unfold round3OuterOriginalEvaluation
    rw [hChart]
    exact ⟨hy.1,hy.2.2.2⟩
  have hp := hControl Data.parameterCount Data.atlas B hd.atlas_smooth hB Data.parameterSet
    RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter S hScompact hS
    ell t hell helt ht1 u hu H hH hHs F0 hF0 a inherited reference ha
    (by simpa only [hChart,hH0] using hInherited)
    (by simpa only [hChart,hH0] using hReference) budget hBudget
  dsimp only at hp
  have hTargetSmooth : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Target i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) := by
    simpa only [Target,hH0,hChart] using hp.2.1
  have hTargetSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (Target p x).IsSymm := by
    intro p _ x
    simpa only [Target,hH0] using hp.2.2.1 p x
  have hTF : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (fun p x => Target p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ := by
    simpa only [Target,hH0,hChart] using hp.2.2.2.2.2.1
  have hTB : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (fun p x => Target p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤
        C*budget*(ell/t)^r+inherited+a*reference := by
    simpa only [Target,hH0,hChart] using hp.2.2.2.2.2.2
  have hGerm : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧ S i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Target i) O :=
    fun i => ⟨incrementsOriginalDifferentiation Data.atlas Data.parameterChart i,
      parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i,
      fun _ (hy : _ ∈ S i) => hy.1,hTargetSmooth i⟩
  have hRefSmooth := parameterRound2_inducedMetric_originalCoordinates_contDiffOn
    Data.atlas Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth F0 hF0
  have hRefGerm : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧ S i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.reference i) O := by
    intro i
    refine ⟨incrementsOriginalDifferentiation Data.atlas Data.parameterChart i,
      parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i,
      fun _ hy => hy.1,?_⟩
    simpa only [hRef,hH0] using hRefSmooth i
  obtain ⟨U,hU,hKU,hUW,hDomain,hQual,hRes⟩ :=
    round3_original_local_retarget_positive_cone_of_C0 Data hd hLinear hDecomp rho hReserve
      Target hTargetSymm hGerm hRefGerm ell ML
      (C*budget*(ell/t)^r+inherited+a*reference) hProfile hML hTF hTB hSmall
  refine ⟨hp.1,hp.2.2.2.1,hp.2.2.2.2.1,U,hU,hKU,hUW,?_,?_,?_⟩
  · exact { source_dim := hDomain.source_dim
            target_dim := hDomain.target_dim
            parameter_open := hDomain.parameter_open
            parameter_compact := hDomain.parameter_compact
            parameter_subset := hDomain.parameter_subset
            atlas_smooth := hDomain.atlas_smooth
            parameter_charts_smooth := hDomain.parameter_charts_smooth
            source_norm_subset := hDomain.source_norm_subset
            source_inner_norm := hDomain.source_inner_norm
            parameter_norm_subset := hDomain.parameter_norm_subset
            parameter_cover := hDomain.parameter_cover
            primary_open := hDomain.primary_open
            cutoff_support_local := hDomain.cutoff_support_local }
  · exact { fiber_open := hQual.fiber_open
            H_symmetric := hQual.H_symmetric
            reference_symmetric := hQual.reference_symmetric
            H_mem := hQual.H_mem
            reference_mem := hQual.reference_mem
            decomposition := hQual.decomposition
            argument_positive := hQual.argument_positive }
  · exact ⟨hRes.reserve_pos,hRes.lower⟩

#print axioms round3Outer_exists_uniform_computed_positive_target
end GlobalEmbedding.Continuation
