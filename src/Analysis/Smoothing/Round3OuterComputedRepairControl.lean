import Smoothing.Round3OuterComputedPositiveTarget
import Smoothing.Round3OuterReferenceC2

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
local instance computedRepairChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance computedRepairIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Same literal SF/SH, actual positive target, and reference C2 closeness.
Together these are the numerical inputs to fixed-reference geometric
stability; no current-SF compact choice enters either bound. -/
theorem round3Outer_exists_uniform_computed_repair_control
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
    ∀ a inherited reference mapInherited budget ML : ℝ, 0 ≤ a →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => u z-F0 z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => u z-F0 z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S).toReal ≤ mapInherited →
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
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => SF z-F0 z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S ≠ ⊤ ∧
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas B.chart (fun z => SF z-F0 z))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S).toReal ≤ C*budget*(ell/t)^r+mapInherited ∧
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
  obtain ⟨C,hC,hPositive⟩ := round3Outer_exists_uniform_computed_positive_target
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS BP0 TP hBS0 hTS hBP0 hTP Ds Dp radius hradius r
  refine ⟨C,hC,?_⟩
  intro Data hd hLinear hDecomp rho hReserve B hChart RS RP hbuffer Omega Q hOmega hQ
    hOT hQT hsource hparameter hScompact ell t hell helt ht1 u hu H hH hHs F0 hF0 hH0 hRef
    a inherited reference mapInherited budget ML ha S hMapFinite hMapBound hInherited hReference
    hBudget hProfile hML hSmall mu K chi SF SH Target
  have hp := hPositive Data hd hLinear hDecomp rho hReserve B hChart RS RP hbuffer
    Omega Q hOmega hQ hOT hQT hsource hparameter hScompact ell t hell helt ht1
    u hu H hH hHs F0 hF0 hH0 hRef a inherited reference budget ML ha
    hInherited hReference hBudget hProfile hML hSmall
  dsimp only at hp
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hSF := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas B.chart
    hd.atlas_smooth hB SF hp.1
  have hF0coord := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas B.chart
    hd.atlas_smooth hB F0 hF0
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas B.chart i := by
    rw [hChart]
    exact fun _ _ hy => hy.1
  have hControl := round3_original_reference_C2_from_tail
    (incrementsOriginalMapCoordinates Data.atlas B.chart u)
    (incrementsOriginalMapCoordinates Data.atlas B.chart SF)
    (incrementsOriginalMapCoordinates Data.atlas B.chart F0)
    (incrementsOriginalDifferentiation Data.atlas B.chart) S
    (parameterRound2_originalDifferentiation_open Data.atlas B.chart) hSO hu hSF hF0coord
    hp.2.1 hMapFinite (C*budget*(ell/t)^r) mapInherited hp.2.2.1 hMapBound
  exact ⟨hp.1,hControl.1,hControl.2,hp.2⟩

#print axioms round3Outer_exists_uniform_computed_repair_control
end GlobalEmbedding.Continuation
