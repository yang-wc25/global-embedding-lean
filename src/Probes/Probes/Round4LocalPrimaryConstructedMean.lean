import Probes.Round4LocalPrimaryCanonicalMean
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
variable {Β : Type*} [Fintype Β]

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

variable {SubSecondary : Type*} [Fintype SubSecondary]

/-- The literal original mean-number formulas and completed secondary
profiles fill every numerical binding automatically. Only the actual
canonical factory output for the same SF/SH is consumed. -/
theorem round4_repair_constructed_original_canonical_mean_local
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference givenPacket : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius0 hradius0 reference givenPacket)
    (hK : Ref.parameterSet=univ) (hOmega : Ref.sourceNormDomain=packet.Omega)
    (hQ : Ref.parameterNormDomain=packet.Q)
    {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (Rsub Lprimary Rsecondary : ℕ) (c cT rho : ℝ) (hrho : 0 < rho)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ j, 0 ≤ Packet j)
    (Input Mrest Kcut Tinv Tobs : ℕ → ℝ) :
    let numbers := round3RepairOriginalMeanNumbers m d N q Rsub Lprimary c cT rho hrho
      Packet Forward Inverse Meta hPacket
    let profile := numbers.complete q Input Rsecondary Mrest Kcut Tinv Tobs
    ∀ (reserved : Round3RepairReservedCosts (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget)
      (state : Round3RepairCurrentSmoothingState packet q budget),
    let uniform := reserved.generated.data state
    ∀ (normal : Fin Ref.primaryCount → P × M → V) (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref (state.smoothedMap packet) (state.computedTarget packet)
      Ref.parameterOpen normal domain neighborhood
    let hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)) := uniform.slice_smooth
    ∀ (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Β)
        (fun p x => Data.F (p,x)))
      (hPreserves : ∀ nu a, Round3ParameterChartPreserves (g.chart nu a))
      (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)),
    Round4ParameterOriginalGeneratedCanonicalSupply Data hF g hS state.ell c cT rho (Packet 0) q Rsub Lprimary
      Packet Forward Inverse Meta →
    ∃ witness : Round3RepairCanonicalMeanWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β)
      (SubSecondary := SubSecondary) packet reserved.generated.cost uniform,
      witness.g=g ∧ witness.primary=Data.primaryDomain := by
  intro numbers profile reserved state uniform normal domain neighborhood Data hF g hPreserves hS generated
  rcases reserved.generated.profiles with
    ⟨hRho,hReserve,hRsub,hLprimary,hRsecondary,hBnd,hMg,hDinput,hT,hRest⟩
  exact round4_repair_original_domains_canonical_mean_local Ref packet state reserved.generated.cost uniform
    hK hOmega hQ normal domain neighborhood g hPreserves hS c cT rho (Packet 0) Rsub Lprimary
    Packet Forward Inverse Meta generated hRho hReserve hRsub hLprimary hBnd hMg hDinput hT

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_repair_constructed_original_canonical_mean_local
