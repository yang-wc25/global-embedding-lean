import Probes.Round4ParameterLiteralPositiveStage
import Probes.Round4ParameterNamedNormalConsumers
import Smoothing.Round3ParameterLiteralCoherentBeforeMetric
import Smoothing.Round3OuterLiteralRawBeforeMetric
import Smoothing.Round4LocalPrimaryLiteralStage

/-!
# The literal raw repair witness uses the finite named normal profile

The same computed SF/SH stage, exact positivity construction, canonical
mean and coherent secondary displacement now consume the named normal
coefficient. The actual raw witness is constructed for every allowed
future repair state, before the prescribed metric is selected. Current
state bounds here are the unchanged internally manufactured repair
invariants, not new assumptions at the original-data endpoint.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [CompactSpace M]
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

private local instance literalRawSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem round4Parameter_literal_coherent_named_normal_before_metric
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (hNormSource : Ref.sourceNormDomain = smoothing.Omega)
    (hNormParameter : Ref.parameterNormDomain = smoothing.Q)
    (hAll : Ref.parameterSet = univ)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref smoothing.domain hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hsRef)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (budget ML : ℝ) (hbudget : 0 ≤ budget)
    (hProfile : incrementsOriginalInputProfileWithLinear Ref 0 1 ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Ref 0 1).toReal ≤ ML) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta),
    let g0 := round3ParameterWholePrimaryFamily Ref smoothing.domain hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref smoothing.domain hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
      (∀ j, 0 ≤ Tinv j) ∧ (∀ j, 0 ≤ Kcut j) ∧ (∀ j, 0 ≤ Tobs j) ∧
    ∀ (k : ℕ) (hk : 10 ≤ k),
    let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
    (∀ j, 0 ≤ Cnormal j) ∧
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ,
      (∀ j, Mrest j = round4ParameterSecondaryGeometryProfile m d N (40*(k+1))
        (fun a : Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary =>
          (secondary.piece a.1 a.2.1 a.2.2).cT/16)
        (fun j => max (Cmap j*budget)
          (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j))))
        Tinv Tobs (lower/4) j) ∧
      (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder (40*(k+1)) j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∃ Cs : ℝ, Cs = 2*round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 (40*(k+1)) ∧
    0 ≤ Cs ∧
    let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
    let sigma := round3RepairComputedGeometryThreshold Cs budget (reference 0) L rho epsilon
    0 < sigma ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Ref.atlas
        smoothing.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i)),
    let changed := smoothing.withMetric metric hSym hSmooth
    ∀ (s : ℕ) (hks : k ≤ s) (t : ℝ) (ht : 0 < t) (htSmall : t ≤ sigma),
    ∀ (oldMap : P × M → Ey) (hOld : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ oldMap)
      (hBudget : (parameterLocalOriginalTotalPairWeighted Ref.atlas changed.parameterFamily oldMap
        (fun p x => ((t^k)^2)⁻¹ • (changed.metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x))
        (40*(k+1)) t (incrementsOriginalEvaluation Ref.atlas changed.parameterFamily.chart
          changed.Omega changed.Q univ)).toReal ≤ budget),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas changed.parameterFamily.chart
      (fun z => oldMap z-changed.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas changed.parameterFamily.chart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas changed.parameterFamily.chart
      (fun z => oldMap z-changed.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas changed.parameterFamily.chart) S).toReal ≤ epsilon/2 →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Ref.atlas Ref.parameterChart
      (fun p x => ((t^k)^2)⁻¹ • (changed.metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x)-Ref.H p x))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ rho/(4*(L+1)) →
    let ht1 : t ≤ 1 := htSmall.trans (min_le_left _ _)
    let state := round3RepairLiteralCurrentState changed k s hk hks t ht ht1 oldMap hOld budget hBudget
    let Data := state.computedData changed Ref.parameterOpen (rho/4)
    let stage := state.toStage changed Ref.parameterOpen (rho/4)
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff _ BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1)) budget reference Given stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => state.smoothedMap changed (p,x)) hF
      (fun p x => Ref.phase nu (p,x)) (Ref.freeNormal nu)
    ∃ out : Round3RepairConstructedPositiveStage changed state rho Cs (epsilon/2),
      out.parameterOpen = Ref.parameterOpen ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas changed.parameterFamily.chart
        (fun z => state.smoothedMap changed z-changed.referenceMap z))
        (incrementsOriginalDifferentiation Ref.atlas changed.parameterFamily.chart) S).toReal ≤ epsilon ∧
      Round4LocalPrimaryCoherentConclusion Ref changed.domain hsRef hnRef theta packet profiles secondary
        (state.smoothedMap changed) (state.computedTarget changed) (round3OriginalPositiveCone Ref (rho/4))
        stage hF normal Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs
        ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1)) lower (rho/4) := by
  intro theta
  have hGiven : ∀ j, 0 ≤ Given j := fun j => ENNReal.toReal_nonneg.trans (smoothing.given_bound j)
  have hF0 : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F := by
    rw [hReferenceMap]
    have hh := smoothing.referenceMap_smooth
    rwa [modelWithCornersSelf_prod] at hh
  have hReference : ∀ p ∈ Ref.parameterOpen, ∀ x, Ref.reference p x ≠ 0 := by
    intro p hp x
    rw [smoothing.reference_eq,smoothing.reference_tensor,← hReferenceMap]
    exact round3_inducedMetric_ne_zero_of_immersion (fun y => Ref.F (p,y)) x (hImmRef.immersion p hp x)
  have hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i) := by
    rw [hNormSource]
    exact smoothing.source_compact
  have hQ : ∀ i, IsCompact (Ref.parameterNormDomain i) := by
    rw [hNormParameter]
    exact smoothing.parameter_compact
  have hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i := by
    rw [hNormSource]
    exact smoothing.source_sampling
  have hParameter : ∀ i, tensorLocalSamplingCoordinates smoothing.parameterFamily i ⊆ Ref.parameterNormDomain i := by
    rw [hNormParameter]
    exact smoothing.parameter_sampling
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    round4Parameter_coherent_with_named_normal_before_order Ref smoothing.domain hsRef hpRef hnRef hImmRef lower hEllRef
      hF0 hAll hReference hLinear Lprimary hLocal BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius
      smoothing.parameterFamily smoothing.chart_eq smoothing.sourcePreparation smoothing.parameterPreparation
      hOmega hQ hSource hParameter smoothing.given_finite smoothing.given_bound
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro k hk
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
  obtain ⟨hCnormal,hByReference⟩ := hByOrder (40*(k+1)) budget hbudget
  let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
  let Ctarget := Cmap
  obtain ⟨hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,hMake⟩ := hByReference reference
  let Cs := 2*round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 (40*(k+1))
  obtain ⟨Cs0,hCsExact,hCs,hLiteral⟩ := round4Parameter_actual_literal_positive_stage
    (n := m+1) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius k hk
  subst Cs0
  have hEntry0 := hLiteral Ref reference Given smoothing hLinear hDecomp rho hReserve
    budget epsilon ML hbudget hepsilon hProfile hML
  refine ⟨hCnormal,hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,Cs,rfl,hCs,hEntry0.1,?_⟩
  intro metric hSym hSmooth changed
  have hEntry := hLiteral Ref reference Given changed hLinear hDecomp rho hReserve
    budget epsilon ML hbudget hepsilon hProfile hML
  intro s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state Data stage hF normal
  obtain ⟨out,hClose⟩ := hEntry.2 s hks t ht htSmall oldMap hOld hBudget hMapFinite hMap hInherited
  have hOpenEq : out.parameterOpen = Ref.parameterOpen := by
    apply Set.Subset.antisymm out.within_reference
    intro p hp
    apply out.contains_parameters
    rw [hAll]
    exact mem_univ _
  have hd : IncrementsOriginalDomainConditions (state.computedData changed Ref.parameterOpen (rho/4)) := by
    rw [← hOpenEq]
    exact out.domain
  have hdec : IncrementsOriginalQualitativeDecompositionInputs
      (state.computedData changed Ref.parameterOpen (rho/4)) := by
    rw [← hOpenEq]
    exact out.decomposition
  have hs := round3_computed_stage_original_smooth_inputs Ref hsRef
    (state.smoothedMap changed) (state.computedTarget changed) Ref.parameterOpen (rho/4) Subset.rfl
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1)) budget reference Given stage
  have hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => state.smoothedMap changed z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ := by
    rw [← changed.chart_eq,hReferenceMap]
    exact out.map_C2_finite
  have hBound : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => state.smoothedMap changed z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon := by
    rw [← changed.chart_eq,hReferenceMap]
    exact hClose
  have hres : IncrementsOriginalDecompositionReserveInputs
      (state.computedData changed Ref.parameterOpen (rho/4)) (rho/4) := by
    rw [← hOpenEq]
    exact out.reserve
  refine ⟨out,hOpenEq,hClose,?_⟩
  exact hMake (state.smoothedMap changed) (state.computedTarget changed)
    (round3OriginalPositiveCone Ref (rho/4)) stage hd hs hdec hFinite hBound (rho/4) hres


theorem round4Parameter_literal_raw_named_normal_before_metric
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (hNormSource : Ref.sourceNormDomain = smoothing.Omega)
    (hNormParameter : Ref.parameterNormDomain = smoothing.Q)
    (hAll : Ref.parameterSet = univ)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref smoothing.domain hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hsRef)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (budget ML : ℝ) (hbudget : 0 ≤ budget)
    (hProfile : incrementsOriginalInputProfileWithLinear Ref 0 1 ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Ref 0 1).toReal ≤ ML) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta),
    let g0 := round3ParameterWholePrimaryFamily Ref smoothing.domain hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref smoothing.domain hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
      (∀ j, 0 ≤ Tinv j) ∧ (∀ j, 0 ≤ Kcut j) ∧ (∀ j, 0 ≤ Tobs j) ∧
    ∀ (k : ℕ) (hk : 10 ≤ k),
    let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
    (∀ j, 0 ≤ Cnormal j) ∧
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ,
      (∀ j, Mrest j = round4ParameterSecondaryGeometryProfile m d N (40*(k+1))
        (fun a : Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary =>
          (secondary.piece a.1 a.2.1 a.2.2).cT/16)
        (fun j => max (Cmap j*budget)
          (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j))))
        Tinv Tobs (lower/4) j) ∧
      (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder (40*(k+1)) j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∃ Cs : ℝ, Cs = 2*round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 (40*(k+1)) ∧
    0 ≤ Cs ∧
    let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
    let sigma := round3RepairComputedGeometryThreshold Cs budget (reference 0) L rho epsilon
    0 < sigma ∧
    ∃ hPacket : ∀ j, 0 ≤ Packet j,
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Ref.atlas
        smoothing.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i)),
    Round4LocalPrimaryLiteralRawStageSupply Ref (smoothing.withMetric metric hSym hSmooth)
      hsRef theta packet profiles secondary
      k Lprimary hk budget ML lower rho hReserve.reserve_pos epsilon Cs
      Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs hPacket := by
  intro theta
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    round4Parameter_literal_coherent_named_normal_before_metric Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear Lprimary hLocal hImmRef
      lower hEllRef rho hReserve budget ML hbudget hProfile hML
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro k hk
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
  let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
  let Ctarget := Cmap
  obtain ⟨hCnormal,hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,Cs,hCsExact,hCs,hSigma,hMake⟩ := hByOrder k hk
  let Packet := fun j => max (Cmap j*budget)
    (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
  have hPacket : ∀ j, 0 ≤ Packet j := fun j =>
    (mul_nonneg (hCmap j) hbudget).trans (le_max_left _ _)
  refine ⟨hCnormal,hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,Cs,hCsExact,hCs,hSigma,hPacket,?_⟩
  intro metric hSym hSmooth
  let changed := smoothing.withMetric metric hSym hSmooth
  intro CtargetReserved numerical reserved hTarget
    s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state
    waveEpsilon delta hWave hWaveTheta
  obtain ⟨out,hOpen,hClose,actual⟩ := hMake metric hSym hSmooth s hks t ht htSmall oldMap hOld hBudget hMapFinite hMap hInherited
  let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
    (fun p x => state.smoothedMap changed (p,x))
    (reserved.generated.data state).slice_smooth
    (fun p x => Ref.phase nu (p,x)) (Ref.freeNormal nu)
  obtain ⟨witness,hPrimary,hEta,hForward,hInverse⟩ :=
    round4_local_primary_coherent_conclusion_repair_increment Ref changed hsRef hnRef
      hAll hNormSource hNormParameter theta packet profiles secondary (by omega)
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1))
      lower (rho/4) (div_pos hReserve.reserve_pos (by norm_num))
      Cnormal _ ForwardC InverseC MetaC hPacket CtargetReserved Mrest Cut Tinv Tobs
      reserved hTarget state normal actual waveEpsilon delta hWave hWaveTheta
  exact ⟨witness⟩


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_literal_coherent_named_normal_before_metric
#print axioms GlobalEmbedding.Continuation.round4Parameter_literal_raw_named_normal_before_metric
