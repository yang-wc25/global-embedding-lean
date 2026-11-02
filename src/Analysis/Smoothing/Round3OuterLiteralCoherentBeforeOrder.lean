import Probes.Round3PreparedOriginalCoherentBeforeOrder
import Smoothing.Round3RepairLiteralStage
import Smoothing.Round3OuterComputedStageOriginalInputs

/-! Original whole-parameter data and the literal (6.5) old-state invariants
produce the SAME positive SF/SH stage, its actual unit normal, every original
primary/doubled/signed phase condition, original coordinate ellipticity, and
its actual canonical mean/raw supply and one coherent physical secondary
choice for every observer and every derivative order. Neither new geometry,
mean estimates, raw pieces nor physical-geometry records are caller inputs. Their fixed costs precede SF and the scale. Both reference packets, their finite labels, the common geometric C2
radius and fixed coordinate profiles precede ALL k. Only the smoothing-order
normal costs and the positive scale cap are then chosen for each k, before
the current map and t. No stagewise infimum or change of finite labels is used. The norm domains are the
literal closed smoothing samples; no estimate is extended from a smaller set. -/

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

theorem round3_actual_original_literal_coherent_before_order
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
    ∃ Cnormal : ℕ → ℝ, (∀ j, 0 ≤ Cnormal j) ∧
    ∃ Cmap : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ, (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder (40*(k+1)) j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∃ Cs : ℝ, 0 ≤ Cs ∧
    let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
    let sigma := round3RepairComputedGeometryThreshold Cs budget (reference 0) L rho epsilon
    0 < sigma ∧ ∀ (s : ℕ) (hks : k ≤ s) (t : ℝ) (ht : 0 < t) (htSmall : t ≤ sigma),
    ∀ (oldMap : P × M → Ey) (hOld : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ oldMap)
      (hBudget : (parameterLocalOriginalTotalPairWeighted Ref.atlas smoothing.parameterFamily oldMap
        (fun p x => ((t^k)^2)⁻¹ • (smoothing.metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x))
        (40*(k+1)) t (incrementsOriginalEvaluation Ref.atlas smoothing.parameterFamily.chart
          smoothing.Omega smoothing.Q univ)).toReal ≤ budget),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun z => oldMap z-smoothing.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun z => oldMap z-smoothing.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart) S).toReal ≤ epsilon/2 →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Ref.atlas Ref.parameterChart
      (fun p x => ((t^k)^2)⁻¹ • (smoothing.metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x)-Ref.H p x))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ rho/(4*(L+1)) →
    let ht1 : t ≤ 1 := htSmall.trans (min_le_left _ _)
    let state := round3RepairLiteralCurrentState smoothing k s hk hks t ht ht1 oldMap hOld budget hBudget
    let Data := state.computedData smoothing Ref.parameterOpen (rho/4)
    let stage := state.toStage smoothing Ref.parameterOpen (rho/4)
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff _ BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1)) budget reference Given stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => state.smoothedMap smoothing (p,x)) hF
      (fun p x => Ref.phase nu (p,x)) (Ref.freeNormal nu)
    ∃ out : Round3RepairConstructedPositiveStage smoothing state rho Cs (epsilon/2),
      out.parameterOpen = Ref.parameterOpen ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        (fun z => state.smoothedMap smoothing z-smoothing.referenceMap z))
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart) S).toReal ≤ epsilon ∧
      Round3ParameterActualCoherentConclusion Ref smoothing.domain hsRef hnRef theta packet profiles secondary
        (state.smoothedMap smoothing) (state.computedTarget smoothing) (round3OriginalPositiveCone Ref (rho/4))
        stage hF normal Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs
        ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) ((Ds+1)*(Dp+1)) lower (rho/4) := by
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
    round3_prepared_actual_original_coherent_before_order Ref smoothing.domain hsRef hpRef hnRef hImmRef lower hEllRef
      hF0 hAll hReference hLinear BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius
      smoothing.parameterFamily smoothing.chart_eq smoothing.sourcePreparation smoothing.parameterPreparation
      hOmega hQ hSource hParameter smoothing.given_finite smoothing.given_bound
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro k hk
  obtain ⟨Cnormal,hCnormal,hByReference⟩ := hByOrder (40*(k+1)) budget hbudget
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,hMake⟩ := hByReference reference
  obtain ⟨Cs,hCs,hLiteral⟩ := round3_exists_uniform_literal_positive_stage
    (n := m+1) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius k hk
  have hEntry := hLiteral Ref reference Given smoothing hLinear hDecomp rho hReserve
    budget epsilon ML hbudget hepsilon hProfile hML
  refine ⟨Cnormal,hCnormal,Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,Cs,hCs,hEntry.1,?_⟩
  intro s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state Data stage hF normal
  obtain ⟨out,hClose⟩ := hEntry.2 s hks t ht htSmall oldMap hOld hBudget hMapFinite hMap hInherited
  have hOpenEq : out.parameterOpen = Ref.parameterOpen := by
    apply Set.Subset.antisymm out.within_reference
    intro p hp
    apply out.contains_parameters
    rw [hAll]
    exact mem_univ _
  have hd : IncrementsOriginalDomainConditions (state.computedData smoothing Ref.parameterOpen (rho/4)) := by
    rw [← hOpenEq]
    exact out.domain
  have hdec : IncrementsOriginalQualitativeDecompositionInputs
      (state.computedData smoothing Ref.parameterOpen (rho/4)) := by
    rw [← hOpenEq]
    exact out.decomposition
  have hs := round3_computed_stage_original_smooth_inputs Ref hsRef
    (state.smoothedMap smoothing) (state.computedTarget smoothing) Ref.parameterOpen (rho/4) Subset.rfl
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1)) budget reference Given stage
  have hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => state.smoothedMap smoothing z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ := by
    rw [← smoothing.chart_eq,hReferenceMap]
    exact out.map_C2_finite
  have hBound : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => state.smoothedMap smoothing z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon := by
    rw [← smoothing.chart_eq,hReferenceMap]
    exact hClose
  have hres : IncrementsOriginalDecompositionReserveInputs
      (state.computedData smoothing Ref.parameterOpen (rho/4)) (rho/4) := by
    rw [← hOpenEq]
    exact out.reserve
  refine ⟨out,hOpenEq,hClose,?_⟩
  exact hMake (state.smoothedMap smoothing) (state.computedTarget smoothing)
    (round3OriginalPositiveCone Ref (rho/4)) stage hd hs hdec hFinite hBound (rho/4) hres

#print axioms round3_actual_original_literal_coherent_before_order
end GlobalEmbedding.Continuation
