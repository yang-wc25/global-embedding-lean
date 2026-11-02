import Smoothing.Round4LocalPrimaryCanonicalFactory
import Probes.Round3RepairCanonicalMean
import Smoothing.Round3ParameterFixedCarrierCanonicalFactory

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

private local instance repairCanonicalOriginalMeanBridgeSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance repairCanonicalOriginalMeanBridgeSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance repairCanonicalOriginalMeanBridgeGeometryFirstNormed : NormedAddCommGroup (Es →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryFirstSpace : NormedSpace ℝ (Es →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryT0Normed : NormedAddCommGroup (Es →L[ℝ] Tdata) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeGeometryT0Space : NormedSpace ℝ (Es →L[ℝ] Tdata) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance repairCanonicalOriginalMeanBridgeCjetNormed : NormedAddCommGroup (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairCanonicalOriginalMeanBridgeCjetSpace : NormedSpace ℝ (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairCanonicalOriginalMeanBridgeCANormed : NormedAddCommGroup
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairCanonicalOriginalMeanBridgeCASpace : NormedSpace ℝ
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairCanonicalOriginalMeanBridgeCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance repairCanonicalOriginalMeanBridgeCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance repairCanonicalOriginalArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance repairCanonicalOriginalArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance repairCanonicalOriginalArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

variable {SubSecondary : Type*} [Fintype SubSecondary]

/-- The actual original canonical mean factory is transported to the
fixed repair Ω/Q domains. Its SAME primary family, global H and exact
native observer domains are retained in the canonical repair witness. -/
theorem round4_repair_original_domains_canonical_mean_local
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference givenPacket : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius0 hradius0 reference givenPacket)
    {q : ℕ} {budget : ℝ} (state : Round3RepairCurrentSmoothingState packet q budget)
    (cost : Round3RepairPrimitiveCosts)
    (uniform : Round3RepairClosedUniformMeanData (Tr := ℝ) (Λ := Fin Ref.primaryCount)
      (Β := Β) (SubSecondary := SubSecondary) packet cost state)
    (hK : Ref.parameterSet = univ)
    (hOmega : Ref.sourceNormDomain = packet.Omega)
    (hQ : Ref.parameterNormDomain = packet.Q)
    (normal : Fin Ref.primaryCount → P × M → V) (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}) :
    let Data : IncrementsOriginalNativeData (m+1) d N M P :=
      round3ParameterStageData Ref (state.smoothedMap packet) (state.computedTarget packet)
        Ref.parameterOpen normal domain neighborhood
    let hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)) := uniform.slice_smooth
    ∀ (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Β)
        (fun p x => Data.F (p,x)))
      (hPreserves : ∀ nu a, Round3ParameterChartPreserves (g.chart nu a))
      (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
      (c cT rho ML : ℝ) (R Lprimary : ℕ) (Packet Forward0 Inverse Meta0 : ℕ → ℝ),
    Round4ParameterOriginalGeneratedCanonicalSupply Data hF g hS state.ell c cT rho ML q R Lprimary
      Packet Forward0 Inverse Meta0 →
    let Forward := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward0 k)
    let Meta := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta0 k)
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s A => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) A Inverse
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Inverse
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Inverse
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    cost.rho=radius → cost.reserve=rho/4 → cost.Rsub=R → cost.Lprimary=Lprimary →
    cost.Bnd=Bnd → cost.Mg=Mg → cost.Dinput=Dinput → cost.T=Tfixed →
    ∃ witness : Round3RepairCanonicalMeanWitness (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β)
      (SubSecondary := SubSecondary) packet cost uniform,
      witness.g=g ∧ witness.primary=Data.primaryDomain := by
  intro Data hF g hPreserves hS c cT rho ML R Lprimary Packet Forward0 Inverse Meta0 generated
    Forward Meta radius Bnd Mg Dinput Tfixed hRho hReserveCost hRsub hPrimary hBnd hMg hDinput hT
  let Supply := fun (B : Fin Ref.parameterCount → OpenPartialHomeomorph P Ep)
      (S : Fin Ref.atlas.count × Fin Ref.parameterCount → Set (Fin (m+1+d) → ℝ))
      (hC : ∀ i, IsCompact (S i))
      (hO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Ref.atlas B i) =>
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Ref.atlas B S univ,
      H.val=state.computedTarget packet →
      Round3ParameterCanonicalMeanRawReserveSupply (Tr := ℝ) Ref.atlas B S univ
        (parameterRound2_originalTensorGermSeminorm Ref.atlas B S univ hC hO state.ell)
        H radius q R Lprimary (rho/4) Bnd Mg Dinput Tfixed
        (fun p x => state.smoothedMap packet (p,x)) uniform.slice_smooth g domain state.ell
  have hTransport : ∀ (B : Fin Ref.parameterCount → OpenPartialHomeomorph P Ep),
      B=Ref.parameterChart →
      ∀ (S : Fin Ref.atlas.count × Fin Ref.parameterCount → Set (Fin (m+1+d) → ℝ)),
      S=incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet →
      ∀ hC hO, Supply B S hC hO := by
    intro B hB S hS' hC hO
    subst B
    subst S
    exact generated
  have hClosed := hTransport packet.parameterFamily.chart packet.chart_eq packet.closedSamples
    (packet.originalSamples_eq_closed hK hOmega hQ).symm packet.closedSamples_compact (fun _ _ hy => hy.1)
  have hRaw := hClosed.2 uniform.H uniform.target_eq
  refine ⟨{ g := g
            chart_preserves := hPreserves
            primary := domain
            canonical := ?_ },rfl,rfl⟩
  rw [hRho,hReserveCost,hRsub,hPrimary,hBnd,hMg,hDinput,hT]
  exact hRaw

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_repair_original_domains_canonical_mean_local
