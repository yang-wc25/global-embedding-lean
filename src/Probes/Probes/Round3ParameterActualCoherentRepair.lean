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

/-- The actual same-g canonical mean and coherent original secondary
factory fill the genuine repair increment witness. Original samples are
identified with the fixed closed Ω/Q samples internally. No final raw atlas,
mean-iterate reserve, high-order Kq bound, or displacement estimate is assumed. -/
theorem round3Parameter_actual_coherent_repair_increment
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference givenPacket : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius0 hradius0 reference givenPacket)
    (hK : Ref.parameterSet=univ) (hOmega : Ref.sourceNormDomain=packet.Omega)
    (hQ : Ref.parameterNormDomain=packet.Q)
    {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (Rsub Rsecondary : ℕ) (c cT rho : ℝ) (hrho : 0 < rho)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ j, 0 ≤ Packet j)
    (Ctarget Mrest Kcut Tinv Tobs : ℕ → ℝ) :
    let numbers := round3RepairOriginalMeanNumbers m d N q Rsub Ref.primaryCount c cT rho hrho
      Packet Forward Inverse Meta hPacket
    let Input := numbers.inputProfile (Parameters := P) (Primaries := Fin Ref.primaryCount) (Refinements := Β)
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (fun j => Ctarget j*budget+(j+1)*packet.closedReferenceProfile j) q hq
    let profile := numbers.complete q Input Rsecondary Mrest Kcut Tinv Tobs
    ∀ (reserved : Round3RepairReservedCosts (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget), reserved.generated.targetCost=Ctarget →
    ∀ state : Round3RepairCurrentSmoothingState packet q budget,
    let uniform := reserved.generated.data state
    ∀ (normal : Fin Ref.primaryCount → P × M → V) (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref (state.smoothedMap packet) (state.computedTarget packet)
      Ref.parameterOpen normal domain neighborhood
    let hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)) := uniform.slice_smooth
    ∀ (hd : IncrementsOriginalDomainConditions Data)
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Β)
        (fun p x => Data.F (p,x)))
      (hPreserves : ∀ nu a, Round3ParameterChartPreserves (g.chart nu a))
      (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)),
    Round3ParameterOriginalGeneratedCanonicalSupply Data hF g hS state.ell c cT rho (Packet 0) q Rsub
      Packet Forward Inverse Meta →
    Round3ParameterCoherentSecondaryOutput (SubSecondary := SubSecondary) Data (fun p x => Data.F (p,x)) hF
      (round3Parameter_restrictPrimaryFamily (fun p x => Data.F (p,x)) g univ isOpen_univ)
      q state.ell univ Mrest Kcut Tinv Tobs Rsecondary
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet) →
    ∀ (epsilon delta : ℝ), 0 < epsilon → epsilon < reserved.generated.cost.Theta →
    ∃ out : Round3RepairRawIncrementWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β)
        (SubSecondary := SubSecondary) packet reserved.generated.cost uniform epsilon delta,
      out.mean.g=g ∧ out.mean.primary=domain := by
  intro numbers Input profile reserved hTarget state uniform normal domain neighborhood Data hF hd g hPreserves hS
    generated coherent epsilon delta he heTheta
  obtain ⟨witness,hG,hPrimary⟩ := round3_repair_constructed_original_canonical_mean
    Ref packet hK hOmega hQ hq Rsub Rsecondary c cT rho hrho Packet Forward Inverse Meta hPacket
    Input Mrest Kcut Tinv Tobs reserved state normal domain neighborhood g hPreserves hS generated
  obtain ⟨choice,hPreserve,family,hChoice⟩ := coherent
  have hTransport : ∀ (g' : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Ref.primaryCount) (Β := Β) (fun p x => Data.F (p,x))), g'=g →
    ∀ S : Fin Ref.atlas.count × Fin Ref.parameterCount → Set (Fin (m+1+d) → ℝ),
    S=incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet →
    ∃ f : ∀ ip : Fin Ref.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p x => Data.F ((Ref.parameterChart ip).symm p,x))
        (fun p => uniform.slice_smooth ((Ref.parameterChart ip).symm p))
        (round3ParameterNativePrimary (fun p x => Data.F (p,x))
          (round3Parameter_restrictPrimaryFamily (fun p x => Data.F (p,x)) g' univ isOpen_univ)
          (Ref.parameterChart ip)) q state.ell
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        Mrest Kcut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)),
      ∀ ip, (f ip).choice=round3ParameterNativeChoices choice (Ref.parameterChart ip) := by
    intro g' hg S hS'
    subst g'
    subst S
    exact ⟨family,hChoice⟩
  obtain ⟨f,hf⟩ := hTransport witness.g hG packet.closedSamples
    (packet.originalSamples_eq_closed hK hOmega hQ).symm
  obtain ⟨out,hMean,hChoiceOut⟩ := round3_repair_explicit_profiles_increment packet numbers Ctarget hq
    Rsecondary Mrest Kcut Tinv Tobs reserved hTarget state witness normal domain neighborhood hd
    choice hPreserve f hf epsilon delta he heTheta
  refine ⟨out,?_,?_⟩
  · rw [hMean]
    exact hG
  · rw [hMean]
    exact hPrimary

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_coherent_repair_increment
