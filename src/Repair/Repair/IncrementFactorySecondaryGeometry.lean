import Repair.IncrementFactoryRegions
import Repair.IncrementActualSecondaryGeometry

/-! Complete actual nonlinear secondary geometry for the SAME weighted
positive reference factory. The original collar, template and transition
inputs manufacture the region, real nonlinear charts, cutoff partition,
reference reserves, and all observed profiles. No signed region or
completed secondary packet is a hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance factoryLiteralRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance factoryLiteralSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

variable (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : (Fin seed.atlas.count × Fin seed.parameterCount) →
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
  (center : (Fin seed.atlas.count × Fin seed.parameterCount) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
  (hseed : RepairReferenceSeedDomains seed)
  (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)


include hF Htensor O K center in
theorem increment_actual_factory_secondary_geometry
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (theta : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, K i ⊆ closedBall (center i) b.modelRadius)
    (hBuffer : ∀ i z, z ∈ K i → ball z b.buffer ⊆ O i)
    (hInner : ∀ i z, z ∈ O i → (seed.atlas.chart i.1).symm z.2 ∈ seed.atlas.inner i.1)
    (B0 Bs : ℝ) (hB0 : 0 ≤ B0) (hBs : 0 ≤ Bs) (hRadius : 0 ≤ b.modelRadius)
    (hCenter : ∀ i, ‖center i‖ ≤ B0)
    (hSourceValue : ∀ ih z, z ∈ seed.sourceNormDomain ih → ‖z‖ ≤ Bs)
    (rho T : ℝ) (hT : 0 < T) (labelBound : ℕ)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound)
    (hProper : ∀ nu mu, nu ≠ mu →
      (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
        tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
        label nu ≠ label mu) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound T ^ label nu
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hAll : data.parameterSet=univ)
      (hFjoint : ContMDiff IJ 𝓘(ℝ,V) ∞ data.F)
      (lower C2 : ℝ) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
      (hEll : IncrementsOriginalCoordinateEllipticityInputs data lower)
      (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates data.atlas data.parameterChart data.F)
        (incrementsOriginalDifferentiation data.atlas data.parameterChart)
        (incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
          data.parameterNormDomain data.parameterSet) ≠ ⊤)
      (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates data.atlas data.parameterChart data.F)
        (incrementsOriginalDifferentiation data.atlas data.parameterChart)
        (incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
          data.parameterNormDomain data.parameterSet)).toReal ≤ C2)
      (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial) (hFirst : Spatial 1 ≤ T)
      (Bp : ℝ) (hBp : 0 ≤ Bp)
      (hParameterValue : ∀ ip z, z ∈ data.parameterNormDomain ip → ‖z‖ ≤ Bp),
    ∃ (packet : Round3PreparedParameterSecondaryPacket data hd hs theta)
      (numeric : IncrementSecondaryReferenceBudget data hd hs theta packet)
      (charts : IncrementSecondaryChartBudget data hd hs theta packet),
      let mu := incrementFactorySignedMu b T
      let buffer := incrementFactorySignedBuffer b Parameter Spatial
      let coordinateBound := incrementFactorySignedCoordinate b B0 Parameter Spatial
      let kernel := incrementFactorySignedKernel b T
      let Phase := incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial
      let Mb := incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial
      let Forward := incrementScalarForwardProfile Mb coordinateBound Phase
      let Inverse := incrementScalarInverseProfile mu Mb coordinateBound Phase
      let B := 1+Forward 1
      numeric.nativeInverse = Inverse ∧
      numeric.cF = lower/B^2 ∧
      numeric.cT = (kernel/(B^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      numeric.MH = actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      charts.forwardProfile = repairEntranceOriginalForwardProfile Bp Forward Parameter Spatial ∧
      charts.inverseProfile = repairEntranceOriginalInverseProfile Bp Bs Inverse Parameter Spatial ∧
      (∀ BS TS BP TP Ds Dp, charts.cutoffProfile BS TS BP TP Ds Dp =
        incrementSecondaryCutoffProfile (Ep × D) mu Mb buffer BS TS BP TP Ds Dp) ∧
      (∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ data.parameterNormDomain i.2) ∧
      (∀ r i, (packet.s r i).card ≤ incrementScalarTotalRefinementBound («Ep» := Ep) (m := m)
        mu Mb b.modelRadius buffer coordinateBound Phase
        (incrementFactorySignedMu_pos b T hT)
        (incrementFactorySignedMb_spec b T B0 Bs labelBound hT.le hB0 hBs hRadius
          Parameter Spatial hParameter hSpatial).1
        (incrementFactorySignedBuffer_pos b Parameter Spatial hParameter)
        (incrementFactorySignedCoordinate_nonneg b B0 hB0 hRadius Parameter Spatial hParameter)
        (incrementFactorySignedPhaseProfile_nonneg b T B0 Bs labelBound hT.le hB0 hBs hRadius
          Parameter Spatial hParameter hSpatial)
        (incrementFactorySignedMb_spec b T B0 Bs labelBound hT.le hB0 hBs hRadius
          Parameter Spatial hParameter hSpatial).2.1
        (incrementFactorySignedMb_spec b T B0 Bs labelBound hT.le hB0 hBs hRadius
          Parameter Spatial hParameter hSpatial).2.2) := by
  intro raw weight data hd hs hAll hFjoint lower C2 hLower hC2 hEll hMapFinite hMap
    Parameter Spatial hParameter hSpatial transition hFirst Bp hBp hParameterValue
  have hRegion := increment_actual_factory_signed_regions b seed hF Htensor S O K center family hseed outer
    hSample hSEval theta hCompact hSmooth hThetaSource hO hK hBuffer hInner B0 Bs hCenter hSourceValue
    rho T hT labelBound label hLabel hProper hd hs Parameter Spatial hParameter transition hFirst
  let region := fun r i => Classical.choice (hRegion r i)
  have hSupport : ∀ i, tsupport (theta i) ⊆ (data.parameterChart i.2).source ×ˢ data.atlas.inner i.1 := by
    intro i z hz
    have hh := hThetaSource i hz
    have ho := hBuffer i _ hh.2 (mem_ball_self b.buffer_pos)
    have hi := hInner i _ ho
    change (seed.atlas.chart i.1).symm (seed.atlas.chart i.1 z.2) ∈ seed.atlas.inner i.1 at hi
    rw [(seed.atlas.chart i.1).left_inv hh.1.2] at hi
    exact ⟨hh.1.1,hi⟩
  have hMb := incrementFactorySignedMb_spec b T B0 Bs labelBound hT.le hB0 hBs hRadius
    Parameter Spatial hParameter hSpatial
  exact increment_actual_secondary_geometry
    (incrementFactorySignedMu b T) (incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial)
    b.modelRadius (incrementFactorySignedBuffer b Parameter Spatial)
    (incrementFactorySignedCoordinate b B0 Parameter Spatial) (incrementFactorySignedKernel b T)
    lower C2 (incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial)
    (incrementFactorySignedMu_pos b T hT) hMb.1
    (incrementFactorySignedBuffer_pos b Parameter Spatial hParameter)
    (incrementFactorySignedCoordinate_nonneg b B0 hB0 hRadius Parameter Spatial hParameter)
    (incrementFactorySignedPhaseProfile_nonneg b T B0 Bs labelBound hT.le hB0 hBs hRadius
      Parameter Spatial hParameter hSpatial) hMb.2.1 hMb.2.2
    (incrementFactorySignedKernel_pos b T hT) hLower hC2
    data hd hs hAll hFjoint hEll hMapFinite hMap theta hCompact hSmooth hSupport region
    Parameter Spatial hParameter hSpatial transition Bp Bs hBp hBs hParameterValue hSourceValue

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_factory_secondary_geometry
