import Repair.EntranceSpatialPrimaryBudget
import Repair.EntranceReferenceMetric

/-!
# The original factory's primary charts enter the numerical reference budget

The original kernel reserve is stated in the original observing chart and
on its actual primary carrier. The actual same packet's inverse transports
that statement to the reference interface; no native frame or Hessian
output bound is assumed. Source sampling and the inner-domain property
are checked against the original observer using the packet's host identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance entranceSpatialBudgetRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance entranceSpatialBudgetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

theorem RepairReferenceSpatialPrimarySupply.numerical_reference_profiles
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ}
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {plateau : Fin Data.primaryCount → P × M → ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    {mu bound : ℝ}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hmu : 0 < mu) (hBound : 0 ≤ bound)
    (hUOpen : ∀ i, U i ⊆ actualOriginalNativeOpen Data i)
    (hOwnerSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (owner nu).source)
    (V : ℝ) (hV : 0 ≤ V) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hSourceValue : ∀ i z, z ∈ U i → ‖z‖ ≤ V)
    (hOwnerValue : ∀ nu i z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu) z‖ ≤ V)
    (hForwardJet : ∀ nu i j, 1 ≤ j → ∀ z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)) z‖ ≤ T j)
    (hInverseJet : ∀ nu i j, 1 ≤ j → ∀ z,
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).target →
      (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).symm z ∈ U i →
      ((Data.parameterChart i.2).symm z.1,(owner nu).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)).symm z‖ ≤ T j)
    (hSamples : ∀ i z, z ∈ U i → parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i)
    (hInner : ∀ i z, z ∈ U i → (Data.atlas.chart i.1).symm z.2 ∈ Data.atlas.inner i.1)
    (kappa : ℝ) (kernel : RepairOriginalPrimaryKernelInputs Data U kappa)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet=univ)
    (hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,D)) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ Data.F)
    (lower C2 : ℝ) (hkappa : 0 < kappa) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data lower)
    (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ C2) :
    let Forward := repairEntranceSpatialNativeForward V (2*(1+2*bound)) T
    let Inverse := repairEntranceSpatialNativeInverse V (2*actualPhaseInverseConstant mu (2*bound)) T
    ∃ profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta s.packet,
      profiles.piece=s.packet.piece ∧
      profiles.cF=lower/(1+Forward 1)^2 ∧
      profiles.cT=(kappa/((1+Forward 1)^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      profiles.MH=actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      profiles.Tinv=Inverse ∧ profiles.Tforward=Forward := by
  intro Forward Inverse
  have hB : 0 ≤ 2*(1+2*bound) := by positivity
  have hI : 0 ≤ 2*actualPhaseInverseConstant mu (2*bound) := by
    have := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*bound by positivity)
    linarith
  have hForward := repairEntranceSpatialNativeForward_nonneg hV hB hT
  have hInverse := repairEntranceSpatialNativeInverse_nonneg hV hI hT
  have hF : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ Data.F := by
    simpa only [modelWithCornersSelf_prod] using hJoint
  have hCoords := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas Data.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Data.F hF
  have hFinite := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet)
    (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart)
    hCompact (fun _ _ hz => hz.1) hCoords 2
  exact repairEntrance_uniform_reference_profiles Forward Inverse hForward hInverse
    kappa lower C2 hkappa hLower hC2 Data hd hs hAll hJoint hEll hFinite hMap theta s.packet
    (s.chart_inputs hmu hBound hUOpen hOwnerSource V hV T hT hSourceValue hOwnerValue
      hForwardJet hInverseJet hSamples hInner kappa kernel)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.numerical_reference_profiles
