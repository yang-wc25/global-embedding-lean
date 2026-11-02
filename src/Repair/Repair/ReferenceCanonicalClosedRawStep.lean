import Repair.ReferenceCanonicalLiteralStage
import Probes.Round3RepairStatePrimitiveInput

/-! A genuine closed repair state is passed directly to the actual literal
raw factory. Its existing C2/defect invariants and its current-order pair
budget supply every entrance internally. The same toSmoothingState, q,
SF/SH, and one actual all-order increment are preserved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
attribute [local irreducible] incrementCanonical_round3ParameterMeanNormCost incrementCanonical_round3ParameterMeanSizeCost
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

private local instance preparedClosedRawSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem referenceCanonical_round4Parameter_literal_closed_raw_step_local
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hOmega : Ref.sourceNormDomain = smoothing.Omega)
    (hQ : Ref.parameterNormDomain = smoothing.Q)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
    (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta)
    (k Lprimary : ℕ) (hk : 10 ≤ k) (budget ML lower rho : ℝ) (hrho : 0 < rho)
    (epsilonGeom Cs : ℝ)
    (Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs : ℕ → ℝ)
    (hPacket : ∀ j, 0 ≤ Packet j)
    (supply : ReferenceCanonicalLocalPrimaryLiteralRawStageSupply Ref smoothing hsRef theta packet profiles secondary
      k Lprimary hk budget ML lower rho hrho epsilonGeom Cs
      Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs hPacket)
    (CtargetReserved : ℕ → ℝ)
    (reserved : ReferenceCanonicalRepairReservedCosts (Tr := ℝ) (Λ := Fin Ref.primaryCount)
      (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
      (SubSecondary := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary)
      smoothing
      (referenceCanonicalLocalPrimaryLiteralRawProfile Ref smoothing hsRef theta packet profiles
        (40*(k+1)) Lprimary (by omega) budget lower (rho/4) (div_pos hrho (by norm_num))
        Packet ForwardC InverseC MetaC hPacket CtargetReserved Mrest Cut Tinv Tobs)
      (40*(k+1)) (by omega) budget)
    (hTarget : reserved.generated.targetCost = CtargetReserved)
    (epsilonRun eta v : ℝ) (hepsilonRun : 0 ≤ epsilonRun)
    (hEpsilon : epsilonRun ≤ epsilonGeom)
    (hEta : eta ≤ rho/(4*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1)))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hvGeom : v ≤ round3RepairComputedGeometryThreshold Cs budget (reference 0)
      (‖actualOriginalCoefficientFunctional (m+1)‖*ML) rho epsilonGeom)
    (hvTheta : v < reserved.generated.cost.Theta^10)
    (state : Round3RepairClosedState smoothing budget epsilonRun eta k v)
    (s : ℕ) (hks : k ≤ s) :
    Nonempty (Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount)
      (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
      (SubSecondary := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary)
      smoothing reserved.generated.cost
      (reserved.generated.data (state.toSmoothingState s hk hks hv hv1))
      (v^(1/10 : ℝ)) (v^k)) := by
  have hSamples := smoothing.originalSamples_eq_closed hAll hOmega hQ
  have hMapFinite : paperAtlasCj 2
      (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        (fun z => state.map z-smoothing.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤ := by
    rw [hSamples]
    exact state.mapDistance_finite
  have hClosedMap : (smoothing.mapDistance state.map).toReal ≤ epsilonGeom/2 := by
    have h0 : 0 ≤ epsilonGeom := hepsilonRun.trans hEpsilon
    have h1 : (epsilonRun/4)*(1-v) ≤ epsilonRun/4 := by
      nlinarith [mul_nonneg hepsilonRun hv.le]
    exact state.map_close.trans (h1.trans (by linarith))
  have hMap : (paperAtlasCj 2
      (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        (fun z => state.map z-smoothing.referenceMap z))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ epsilonGeom/2 := by
    rw [hSamples]
    exact hClosedMap
  have hInherited : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Ref.atlas Ref.parameterChart
        (fun p x => ((v^k)^2)⁻¹ •
          (smoothing.metric p x-inducedMetric (I := 𝓙) (fun y => state.map (p,y)) x)-Ref.H p x))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤
      rho/(4*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1)) := by
    rw [hSamples,← smoothing.chart_eq]
    exact state.defect_close.trans hEta
  have hEntry := (actual_repair_uniform_stage_threshold
    reserved.generated.cost.theta_pos reserved.generated.cost.theta_le_one).2.2 v hv hvTheta
  exact supply CtargetReserved reserved hTarget s hks v hv hvGeom state.map state.smooth
    state.pair_budget hMapFinite hMap hInherited (v^(1/10 : ℝ)) (v^k) hEntry.1 hEntry.2.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.referenceCanonical_round4Parameter_literal_closed_raw_step_local
