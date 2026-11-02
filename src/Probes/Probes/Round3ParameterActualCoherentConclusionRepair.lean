import Smoothing.Round3ParameterActualStageRawConsumer
import Probes.Round3ParameterActualCoherentRepair
import Probes.Round3RepairExplicitProfilesIncrement
import Probes.Round3RepairConstructedCanonicalMean
import Probes.Round3ParameterSecondaryNoBaseChart
import Probes.Round3RepairOriginalCanonicalMean
import Smoothing.Round3RepairOriginalMeanNumbers
import Probes.Round3RepairReservedCosts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance repairConstructedOriginalMeanBridgeSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance repairConstructedOriginalMeanBridgeSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance repairConstructedOriginalMeanBridgeGeometryFirstNormed : NormedAddCommGroup (Es →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryFirstSpace : NormedSpace ℝ (Es →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryT0Normed : NormedAddCommGroup (Es →L[ℝ] Tdata) := inferInstance
private local instance repairConstructedOriginalMeanBridgeGeometryT0Space : NormedSpace ℝ (Es →L[ℝ] Tdata) := inferInstance
private local instance repairConstructedOriginalMeanBridgeCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance repairConstructedOriginalMeanBridgeCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance repairConstructedOriginalMeanBridgeCjetNormed : NormedAddCommGroup (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairConstructedOriginalMeanBridgeCjetSpace : NormedSpace ℝ (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairConstructedOriginalMeanBridgeCANormed : NormedAddCommGroup
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairConstructedOriginalMeanBridgeCASpace : NormedSpace ℝ
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairConstructedOriginalMeanBridgeCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance repairConstructedOriginalMeanBridgeCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance repairConstructedOriginalArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairConstructedOriginalArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairConstructedOriginalArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup


private local instance conclusionSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- The completed original coherent stage is consumed directly. The
same global primary family and its fixed reference eta/chart functions
survive into the genuine raw increment witness used by the actual repair. -/
theorem round3Parameter_actual_coherent_conclusion_repair_increment
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference givenPacket : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius0 hradius0 reference givenPacket)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hsRef)
    (hK : Ref.parameterSet=univ) (hOmega : Ref.sourceNormDomain=smoothing.Omega)
    (hQ : Ref.parameterNormDomain=smoothing.Q)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
    (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta)
    {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (R L : ℕ) (lower rho : ℝ) (hrho : 0 < rho)
    (Cnormal Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ j, 0 ≤ Packet j)
    (Ctarget Mrest Kcut Tinv Tobs : ℕ → ℝ) :
    let Β := Round3ParameterWholePrimaryIndex Ref theta packet
    let Sub := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary
    let numbers := round3RepairOriginalMeanNumbers m d N q R Ref.primaryCount (lower/4) (profiles.cT/16) rho hrho
      Packet Forward Inverse Meta hPacket
    let Input := numbers.inputProfile (Parameters := P) (Primaries := Fin Ref.primaryCount) (Refinements := Β)
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (fun j => Ctarget j*budget+(j+1)*smoothing.closedReferenceProfile j) q hq
    let numerical := numbers.complete q Input (L*5^Module.finrank ℝ (Ep × Es)) Mrest Kcut Tinv Tobs
    ∀ (reserved : Round3RepairReservedCosts (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
      smoothing numerical q hq budget), reserved.generated.targetCost=Ctarget →
    ∀ state : Round3RepairCurrentSmoothingState smoothing q budget,
    let uniform := reserved.generated.data state
    let stage := state.toStage smoothing Ref.parameterOpen rho
    let hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => state.smoothedMap smoothing (p,x)) := uniform.slice_smooth
    ∀ normal : Fin Ref.primaryCount → P × M → V,
    Round3ParameterActualCoherentConclusion Ref smoothing.domain hsRef hnRef theta packet profiles secondary
      (state.smoothedMap smoothing) (state.computedTarget smoothing) (round3OriginalPositiveCone Ref rho)
      stage hF normal Cnormal Forward Inverse Meta Packet Mrest Kcut Tinv Tobs R L lower rho →
    ∀ (epsilon delta : ℝ), 0 < epsilon → epsilon < reserved.generated.cost.Theta →
    let g0 := round3ParameterWholePrimaryFamily Ref smoothing.domain hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref smoothing.domain hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    ∃ out : Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β)
        (SubSecondary := Sub) smoothing reserved.generated.cost uniform epsilon delta,
      out.mean.primary=domain ∧ out.mean.g.eta=(fun nu => round3FixedCarrierCutoff (g0.eta nu)) ∧
      (∀ nu a, ((out.mean.g.chart nu a) : P × M → P × Es)=g0.chart nu a) ∧
      (∀ nu a, ((out.mean.g.chart nu a).symm : P × Es → P × M)=(g0.chart nu a).symm) := by
  intro Β Sub numbers Input numerical reserved hTarget state uniform stage hF normal actual epsilon delta he heTheta g0 domain
  obtain ⟨rebound,hImm,hPhase,hEll,g,hEta,hForward,hInverse,hGeom,hProfiles,hSupply,hCoherent⟩ := actual
  obtain ⟨out,hG,hPrimary⟩ := round3Parameter_actual_coherent_repair_increment
    Ref smoothing hK hOmega hQ hq R (L*5^Module.finrank ℝ (Ep × Es)) (lower/4) (profiles.cT/16) rho hrho
    Packet Forward Inverse Meta hPacket Ctarget Mrest Kcut Tinv Tobs reserved hTarget state normal domain
    (round3OriginalPositiveCone Ref rho) rebound.domain_conditions g hGeom.preserves stage.samples_compact
    hSupply hCoherent epsilon delta he heTheta
  refine ⟨out,hPrimary,?_,?_,?_⟩
  · rw [hG]
    exact hEta
  · rw [hG]
    exact hForward
  · rw [hG]
    exact hInverse

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_coherent_conclusion_repair_increment
