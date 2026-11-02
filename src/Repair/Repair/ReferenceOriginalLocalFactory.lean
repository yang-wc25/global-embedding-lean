import Repair.ReferenceOriginalLocalFactoryBudget
import Repair.ReferenceActualNormal

/-!
# The actual local reference factory from the original paper norm inputs

This module calls the existing Round4 allowed-class construction.  Every
finite piece, local template, chart, square partition and normal carrier
is produced from the original low bounds.  The old local hierarchical
labels are discarded; later global product coloring supplies the one
hierarchy shared by all original source and parameter hosts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance localFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance localFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance localFactoryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance localFactoryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance localFactoryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance localFactoryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

def repairReferenceFactoryField
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (z : X) :
    (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ) :=
  (round4ActualPhaseOperatorInChart (fun p x => seed.F0 ((seed.parameterChart i.2).symm p,x))
      (fun _ => seed.atlas.chart i.1) z,
    round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor i z)

structure RepairReferenceOriginalLocalFactory
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (O K : Set X) (center : X) where
  s : Finset X
  pick : s → b.cover.indices
  charts : ∀ z : s, ∀ a : Edge, Round4UniformTemplateChart b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
    (repairReferenceFactoryField seed Htensor i) O z.val b.radius (pick z) a
  W : Set X
  card : s.card ≤ b.pieceBound
  centers : (↑s : Set X) ⊆ K
  open_partition : IsOpen W
  cover : K ⊆ W
  partition_domain : W ⊆ O
  operator_bound : ∀ y ∈ O, ‖(repairReferenceFactoryField seed Htensor i y).1‖ ≤ b.operatorBound
  square_partition : ∀ x ∈ W, ∑ z : s, round4RefinementSquareCutoff X s b.cutoffRadius z x ^ 2 = 1
  cutoff_smooth : ∀ z : s, ContDiff ℝ ∞ (round4RefinementSquareCutoff X s b.cutoffRadius z)
  local_count : ∀ x : X, (activeCutoffIndices (round4RefinementSquareCutoff X s b.cutoffRadius) x).card ≤
    5^Module.finrank ℝ X
  normal : ∀ (z : s) a, Round4ActualNormalCarrier
    (fun p x => seed.F0 ((seed.parameterChart i.2).symm p,x))
    (fun p => hF ((seed.parameterChart i.2).symm p))
    (seed.atlas.chart i.1) (charts z a).chart
    (fun y => (b.cover.template (pick z)).covectors a (seed.atlas.chart i.1 y.2))
    z.val b.normalRadius b.firstReserve b.transverseReserve
  normal_support : ∀ (z : s) a, tsupport (round4RefinementSquareCutoff X s b.cutoffRadius z) ⊆
    round4NormalCutoffCarrier (charts z a).chart z.val b.normalRadius
  normal_jets : ∀ (j : ℕ) (Rj : ℝ), 0 ≤ Rj →
    paperAtlasCj (j+2) (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal Rj →
    ∀ (z : s) a k, k ≤ j → ∀ y ∈ round4NormalCutoffCarrier (charts z a).chart z.val b.normalRadius,
      ‖iteratedFDeriv ℝ k (round4ActualNormalCarrierHostField
        (fun p x => seed.F0 ((seed.parameterChart i.2).symm p,x))
        (fun p => hF ((seed.parameterChart i.2).symm p))
        (seed.atlas.chart i.1) (charts z a).chart
        (fun y => (b.cover.template (pick z)).covectors a (seed.atlas.chart i.1 y.2))
        z.val b.normalRadius b.firstReserve b.transverseReserve (normal z a)) y‖ ≤
      round4NativeNormalHostConstant m N j b.firstReserve b.transverseReserve b.forward b.inverse
        (actualOriginalMapJetCost (m+1) d N j*Rj)
  cutoff_jets : ∀ (z : s) j y,
    ‖iteratedFDeriv ℝ j (round4RefinementSquareCutoff X s b.cutoffRadius z) y‖ ≤ b.cutoffProfile j
  chart_profiles : ∀ B0 : ℝ, ‖center‖ ≤ B0 → ∀ (z : s) a,
    (∀ j y, y ∈ (charts z a).chart.source → ‖iteratedFDeriv ℝ j (charts z a).chart y‖ ≤
      round4LinearPhaseForwardProfile b.cover.covectorBound (B0+b.modelRadius+b.radius) j) ∧
    (∀ j y, y ∈ (charts z a).chart.target → ‖iteratedFDeriv ℝ j (charts z a).chart.symm y‖ ≤
      round4LinearPhaseInverseProfile b.covectorLower b.cover.covectorBound (B0+b.modelRadius+b.radius) j)

def RepairReferenceOriginalLocalFactory.actualNormal
    {b : RepairReferenceFactoryBudget m d N}
    {seed : RepairOriginalReferenceSeed (m+1) d N M P}
    {hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x))}
    {Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    {S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ)}
    {i : Fin seed.atlas.count × Fin seed.parameterCount} {O K : Set X} {center : X}
    (localData : RepairReferenceOriginalLocalFactory b seed hF Htensor S i O K center)
    (z : localData.s) (a : Edge) :
    RepairReferenceActualNormal seed hF (seed.parameterChart i.2) (seed.atlas.chart i.1)
      ((b.cover.template (localData.pick z)).covectors a) where
  chart := (localData.charts z a).chart
  center := z.val
  radius := b.normalRadius
  cF := b.firstReserve
  cT := b.transverseReserve
  chart_smooth := (localData.charts z a).smooth
  carrier := localData.normal z a

theorem repair_reference_original_local_factory
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0 i)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart i))
    (hC3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.mapC3)
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hTensorCoords : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor a)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart a))
    (hC1 : paperAtlasCj 1 (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.tensorC1)
    (hSymm : ∀ p x, (Htensor p x).IsSymm)
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (hhost : seed.atlas.chart i.1 ∈ IsManifold.maximalAtlas I ∞ M)
    (O K : Set X) (center : X)
    (hO : IsOpen O) (hConv : Convex ℝ O)
    (hSample : ∀ z ∈ O, parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hKball : K ⊆ closedBall center b.modelRadius)
    (hBuffer : ∀ x ∈ K, ball x b.buffer ⊆ O)
    (hPhase : ∀ x ∈ K, b.phaseMargin ≤ bestPhaseSupremum (repairReferenceFactoryField seed Htensor i x).1)
    (hPositive : ∀ x ∈ K, ∀ v : D,
      b.tensorLower*‖v‖^2 ≤ round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor i x v v)
    (hFirst : ∀ z ∈ O, ∀ v : D, b.firstLower*‖v‖^2 ≤
      ‖fderiv ℝ ((fun x => seed.F0 ((seed.parameterChart i.2).symm z.1,x)) ∘
        (seed.atlas.chart i.1).symm) z.2 v‖^2) :
    Nonempty (RepairReferenceOriginalLocalFactory b seed hF Htensor S i O K center) := by
  obtain ⟨s,pick,charts,W,label,hBase,hRest⟩ :=
    round4_original_pair_low_class_assembly seed.atlas seed.parameterChart seed.F0 hF S hSO hCoords
      b.mapC3 b.mapC3_nonneg hC3 i hhost b.templateDim b.phaseMargin b.tensorLower
      b.phaseMargin_pos b.tensorLower_pos Htensor hTensorCoords b.tensorC1 b.tensorC1_nonneg hC1 hSymm
      b.modelRadius b.buffer b.firstLower b.buffer_pos b.firstLower_pos b.ambientDim O K center
      hO hConv hSample hKball hBuffer hPhase hPositive hFirst
  rcases hBase with ⟨hCard,hCenters,hOpen,hCover,_,_,hPartition,hSmooth,hCount,_⟩
  rcases hRest with ⟨normal,hSupport,_,_,hNormalJets,hCutoffJets,hDomain,_,_,_,_,hProfiles,_⟩
  have hJoint := round4_original_native_host_joint_smooth seed.atlas seed.parameterChart
    seed.F0 S hSO hCoords i O hSample
  have hC2 : ∀ z ∈ O, ‖iteratedFDeriv ℝ 2 (round3OriginalNativeMapCoordinates
      seed.atlas seed.parameterChart seed.F0 i) z‖ ≤ b.nativeMap3 := by
    intro z hz
    exact round4_original_C3_native_joint_jets seed.atlas seed.parameterChart seed.F0 S hSO hCoords
      b.mapC3 b.mapC3_nonneg hC3 i 2 (by omega) z (hSample z hz)
  exact ⟨{
    s := s
    pick := pick
    charts := charts
    W := W
    card := hCard
    centers := hCenters
    open_partition := hOpen
    cover := hCover
    partition_domain := hDomain
    operator_bound := fun z hz => round4_actual_phase_operator_norm_from_joint_C2
      (fun p x => seed.F0 ((seed.parameterChart i.2).symm p,x)) (seed.atlas.chart i.1)
      O hO hJoint b.nativeMap3 hC2 z hz
    square_partition := hPartition
    cutoff_smooth := hSmooth
    local_count := hCount
    normal := normal
    normal_support := hSupport
    normal_jets := hNormalJets
    cutoff_jets := hCutoffJets
    chart_profiles := hProfiles }⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_local_factory
