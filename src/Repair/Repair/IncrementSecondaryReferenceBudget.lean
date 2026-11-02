import Repair.IncrementNumericalSecondaryPacket
import Repair.IncrementUniformSecondaryStability

/-! The common reference values read by the actual secondary stability and
solver factories. The numerical packet producer supplies these fields by
literal value equalities, not by current-map output estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)


structure IncrementSecondaryReferenceBudget
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta) where
  nativeInverse : ℕ → ℝ
  nativeInverse_nonneg : ∀ j, 0 ≤ nativeInverse j
  cF : ℝ
  cT : ℝ
  MH : ℝ
  cF_pos : 0 < cF
  cT_pos : 0 < cT
  MH_nonneg : 0 ≤ MH
  first_value : ∀ r i a, (packet.piece r i a).cF = cF
  transverse_value : ∀ r i a, (packet.piece r i a).cT = cT
  hessian_bound : ∀ r i a, (packet.piece r i a).MH ≤ MH
  inverse_bound : ∀ r i a j, 1 ≤ j → j ≤ 2 → (packet.piece r i a).Tinv j ≤ nativeInverse j

def incrementSecondaryStabilityTolerance
    {Ref : IncrementsOriginalNativeData (m+1) d N M P}
    {hd : IncrementsOriginalDomainConditions Ref} {hs : IncrementsOriginalSmoothInputs Ref}
    {theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ}
    {packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta}
    (budget : IncrementSecondaryReferenceBudget Ref hd hs theta packet) : ℝ :=
  repairEntranceGeometryTolerance m d N budget.nativeInverse budget.cF budget.cT budget.MH
    budget.cF_pos budget.cT_pos

theorem incrementSecondaryStabilityTolerance_pos
    {Ref : IncrementsOriginalNativeData (m+1) d N M P}
    {hd : IncrementsOriginalDomainConditions Ref} {hs : IncrementsOriginalSmoothInputs Ref}
    {theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ}
    {packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta}
    (budget : IncrementSecondaryReferenceBudget Ref hd hs theta packet) :
    0 < incrementSecondaryStabilityTolerance budget :=
  repairEntranceGeometryTolerance_pos m d N budget.nativeInverse budget.nativeInverse_nonneg
    budget.cF budget.cT budget.MH budget.cF_pos budget.cT_pos budget.MH_nonneg

def incrementNumericalSecondaryBudget
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (lower C2 : ℝ) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (old : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (chart : ∀ r i a, IncrementSecondaryNativeChartInputs Ref hd hs i r _
      (old.piece r i a) Forward Inverse)
    (cT : ℝ) (hcT : 0 < cT) (hReserve : ∀ r i a, (old.piece r i a).cT = cT) :
    IncrementSecondaryReferenceBudget Ref hd hs theta
      (incrementNumericalSecondaryPacket Forward Inverse hForward hInverse lower C2 hLower hC2
        Ref hd hs hAll hFjoint hEll hMapFinite hMap theta old chart) := by
  have hB : 0 < 1+Forward 1 := by have := hForward 1; linarith
  exact {
    nativeInverse := Inverse
    nativeInverse_nonneg := hInverse
    cF := lower/(1+Forward 1)^2
    cT := cT
    MH := actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2)
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    cT_pos := hcT
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hInverse 1)
      (mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2)
    first_value := fun _ _ _ => rfl
    transverse_value := hReserve
    hessian_bound := fun _ _ _ => le_rfl
    inverse_bound := fun _ _ _ _ _ _ => le_rfl }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementNumericalSecondaryBudget
