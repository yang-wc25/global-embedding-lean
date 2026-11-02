import Smoothing.Round3OuterLiteralCoherentBeforeOrder
import Probes.Round3ParameterActualCoherentConclusionRepair
import Smoothing.Round3RepairLiteralStage
import Smoothing.Round3OuterComputedStageOriginalInputs

/-! The literal original old state now supplies a genuine RawIncrementWitness.
The primary/secondary packets, fixed carriers and common geometric tolerance
precede every smoothing order. For each order the numerical geometry profiles
precede the current map and scale. The separately selected repair target cost
is used only for the actual mean-input budget; it need not equal the canonical
stage's target-profile constant. No raw witness, prepared piece or desired
increment estimate is a premise. -/

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

/-- The numerical profiles used by the same canonical mean and actual
secondary choice. The reserved-target coefficient is independent of the
stage coefficient already absorbed into Packet. -/
def round3OuterLiteralRawProfile
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
    (q : ℕ) (hq : 1 ≤ q) (budget lower rho : ℝ) (hrho : 0 < rho)
    (Packet ForwardC InverseC MetaC : ℕ → ℝ) (hPacket : ∀ j, 0 ≤ Packet j)
    (CtargetReserved Mrest Cut Tinv Tobs : ℕ → ℝ) : Round3RepairPrimitiveProfiles :=
  let numbers := round3RepairOriginalMeanNumbers m d N q
    ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Ref.primaryCount
    (lower/4) (profiles.cT/16) rho hrho Packet ForwardC InverseC MetaC hPacket
  let Input := numbers.inputProfile (Parameters := P) (Primaries := Fin Ref.primaryCount)
    (Refinements := Round3ParameterWholePrimaryIndex Ref theta packet)
    (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    (fun j => CtargetReserved j*budget+(j+1)*smoothing.closedReferenceProfile j) q hq
  numbers.complete q Input (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) Mrest Cut Tinv Tobs

/-- Fixed-order actual old-state entrance with a genuine same-stage repair
witness as conclusion. The numerical packet and geometry cap are fixed. -/
def Round3OuterLiteralRawStageSupply
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
    (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta)
    (k : ℕ) (hk : 10 ≤ k) (budget ML lower rho : ℝ) (hrho : 0 < rho) (epsilon Cs : ℝ)
    (Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs : ℕ → ℝ)
    (hPacket : ∀ j, 0 ≤ Packet j) : Prop :=
    let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
    let sigma := round3RepairComputedGeometryThreshold Cs budget (reference 0) L rho epsilon
    ∀ CtargetReserved : ℕ → ℝ,
    let numerical := round3OuterLiteralRawProfile Ref smoothing hsRef theta packet profiles
      (40*(k+1)) (by omega) budget lower (rho/4) (div_pos hrho (by norm_num))
      Packet ForwardC InverseC MetaC hPacket CtargetReserved Mrest Cut Tinv Tobs
    ∀ (reserved : Round3RepairReservedCosts (Tr := ℝ) (Λ := Fin Ref.primaryCount)
      (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
      (SubSecondary := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary)
      smoothing numerical (40*(k+1)) (by omega) budget),
    reserved.generated.targetCost=CtargetReserved →
    ∀ (s : ℕ) (hks : k ≤ s) (t : ℝ) (ht : 0 < t) (htSmall : t ≤ sigma),
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
    ∀ (waveEpsilon delta : ℝ), 0 < waveEpsilon → waveEpsilon < reserved.generated.cost.Theta →
    Nonempty (Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount)
      (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
      (SubSecondary := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary)
      smoothing reserved.generated.cost (reserved.generated.data state) waveEpsilon delta)

theorem round3_actual_original_literal_raw_before_order
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
    0 < sigma ∧
    ∃ hPacket : ∀ j, 0 ≤ Packet j,
    Round3OuterLiteralRawStageSupply Ref smoothing hsRef theta packet profiles secondary
      k hk budget ML lower rho hReserve.reserve_pos epsilon Cs
      Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs hPacket := by
  intro theta
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    round3_actual_original_literal_coherent_before_order Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear hImmRef
      lower hEllRef rho hReserve budget ML hbudget hProfile hML
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro k hk
  obtain ⟨Cnormal,hCnormal,Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,Cs,hCs,hSigma,hMake⟩ := hByOrder k hk
  let Packet := fun j => max (Cmap j*budget)
    (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
  have hPacket : ∀ j, 0 ≤ Packet j := fun j =>
    (mul_nonneg (hCmap j) hbudget).trans (le_max_left _ _)
  refine ⟨Cnormal,hCnormal,Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,Cs,hCs,hSigma,hPacket,?_⟩
  intro CtargetReserved numerical reserved hTarget
    s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state
    waveEpsilon delta hWave hWaveTheta
  obtain ⟨out,hOpen,hClose,actual⟩ := hMake s hks t ht htSmall oldMap hOld hBudget hMapFinite hMap hInherited
  let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
    (fun p x => state.smoothedMap smoothing (p,x))
    (reserved.generated.data state).slice_smooth
    (fun p x => Ref.phase nu (p,x)) (Ref.freeNormal nu)
  obtain ⟨witness,hPrimary,hEta,hForward,hInverse⟩ :=
    round3Parameter_actual_coherent_conclusion_repair_increment Ref smoothing hsRef hnRef
      hAll hNormSource hNormParameter theta packet profiles secondary (by omega)
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) ((Ds+1)*(Dp+1))
      lower (rho/4) (div_pos hReserve.reserve_pos (by norm_num))
      Cnormal _ ForwardC InverseC MetaC hPacket CtargetReserved Mrest Cut Tinv Tobs
      reserved hTarget state normal actual waveEpsilon delta hWave hWaveTheta
  exact ⟨witness⟩

#print axioms round3_actual_original_literal_raw_before_order
end GlobalEmbedding.Continuation
