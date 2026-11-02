import OriginalCollars.FactoryPrimaryCarrier
import OriginalIncrements.CommonGeometryPrimarySupply
import OriginalIncrements.FactoryOriginalGeometry

/-!
# The actual factory manufactures one common primary grid geometry

The plateau buffer, literal phase lower bound and low full joint jets are
proved on the same weighted original datum. The common numbers are fixed
from the factory budget and original transition profiles before the grid
is chosen. The resulting geometry is consumed by the actual counted-grid
constructor; no old packet is relabeled and no adapted estimate is assumed.

The construction domains use only the original spatial source samples.
They are not required to lie over the compact parameter evaluation set.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

namespace OriginalIncrements
open OriginalCollars

/-- Original-coordinate geometry sufficient to run the counted primary
grid at prescribed common numbers. Every bound concerns the original
literal phase, not a chosen inverse or the final increment. -/
structure OriginalCommonPrimaryGeometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (mu Mb R buffer : ℝ) where
  mu_pos : 0 < mu
  Mb_nonneg : 0 ≤ Mb
  radius_pos : 0 < R
  buffer_pos : 0 < buffer
  region : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X
  open_region : ∀ nu i, IsOpen (region nu i)
  native : ∀ nu i, region nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i
  radius : ∀ nu i, originalNativePrimaryCarrier Data i nu
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R
  buffered : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      ball x buffer ⊆ region nu i
  noncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖
  first : ∀ nu i x, x ∈ region nu i →
    ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb
  second : ∀ nu i x, x ∈ region nu i →
    buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb

/-- The original geometry runs the actual grid and keeps all numerical
fields and the native forward bound of that very packet. -/
theorem OriginalCommonPrimaryGeometry.exists_counted_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (mu Mb R buffer : ℝ)
    (g : OriginalCommonPrimaryGeometry Data theta mu Mb R buffer) :
    ∃ supply : OriginalCountedPrimarySupply Data theta,
      (∀ nu i, supply.mu nu i = mu) ∧
      (∀ nu i, supply.Mb nu i = Mb) ∧
      (∀ nu i, supply.buffer nu i = buffer) ∧
      (∀ nu i, supply.radius nu i = R) ∧
      (∀ nu i a, (supply.packet.piece nu i a).Bnative = 2*(1+2*Mb)) :=
  original_open_counted_primary_supply_from_common_geometry mu Mb R buffer g.mu_pos
    g.Mb_nonneg g.radius_pos g.buffer_pos Data hd hs theta hCompact hSmooth hSupport
    g.region g.open_region g.native g.radius g.buffered g.noncritical g.first g.second

end OriginalIncrements

namespace OriginalCollars
open OriginalIncrements

variable [RiemannianBundle
  (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

/-- The actual original factory produces the numerical common geometry
and original kernel reserve from original transition profiles. This
constructor contains the buffer and positive-jet proofs; neither is an
output-shaped input hypothesis. -/
theorem original_factory_primary_common_geometry
    (b : RepairReferenceFactoryBudget m d N) (cap B0 : ℝ) (hCap : 0 ≤ cap)
    (Parameter Spatial Joint : ℕ → ℝ)
    (hSpatial : ∀ j, 0 ≤ Spatial j) (hJoint : ∀ j, 0 ≤ Joint j)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : Fin seed.atlas.count × Fin seed.parameterCount → Set X)
    (center : Fin seed.atlas.count × Fin seed.parameterCount → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSourceSample : ∀ i z, z ∈ O i → z.2 ∈ seed.sourceNormDomain i.1)
    (outer theta : Fin seed.atlas.count × Fin seed.parameterCount → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, K i ⊆ closedBall (center i) b.modelRadius)
    (hCenter : ∀ i, ‖center i‖ ≤ B0)
    (hBuffer : ∀ i z, z ∈ K i → ball z b.buffer ⊆ O i)
    (hTransition : ∀ nu i z, z ∈ O i → ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ Joint j)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeightLow : ∀ nu, 1 ≤ weight nu) (hWeightHigh : ∀ nu, |weight nu| ≤ cap) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    let buffer := repairReferenceFactoryInteractionBuffer b Joint
    let mu := b.covectorLower/(1+Spatial 1)
    let Mb := originalFactoryPrimaryPhaseBudget cap b.cover.covectorBound buffer Spatial
    let R := 1+|B0|+|b.modelRadius|
    let kappa := b.cover.restrictionReserve/(1+Spatial 1)^2
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hOOpen : ∀ i, O i ⊆ actualOriginalNativeOpen data i)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial),
      Nonempty (OriginalCommonPrimaryGeometry data theta mu Mb R buffer) ∧
      0 < kappa ∧ RepairOriginalPrimaryKernelInputs data (actualOriginalNativeOpen data) kappa := by
  intro raw data buffer mu Mb R kappa hd hs hOOpen transition
  have hbuffer : 0 < buffer := repairReferenceFactoryInteractionBuffer_pos b Joint hJoint
  have hT : 0 < 1+Spatial 1 := by linarith [hSpatial 1]
  obtain ⟨hmu,hkappa,hMb,hKernel,hGeometry⟩ :=
    original_factory_primary_geometry_from_source_samples b cap buffer (1+Spatial 1) hCap
      hbuffer.le hT Parameter Spatial hSpatial (by linarith) seed hF Htensor S O K center family
      hseed outer rho weight hWeightLow hWeightHigh hSourceSample hd hs transition
  have hSupply := original_factory_primary_common_carrier b seed hF Htensor S O K center family
    hseed hSO hSample outer theta hCompact hSmooth hThetaSource hO hK hBuffer Joint hJoint
    hTransition rho weight hd hOOpen
  choose U hPositive hCompactCarrier hOpenU hRadiusU hBallU hSubU hTargetU hMapU hUpperU
    hNonemptyU using hSupply
  have hRadius : ∀ nu i, originalNativePrimaryCarrier data i nu
      (round3ParameterNativeParent (data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R := by
    intro nu i z hz
    have hDistance := mem_closedBall.mp (hRadiusU nu i hz)
    have hTriangle := dist_triangle z (center i) (0 : X)
    simp only [dist_zero_right] at hTriangle
    rw [mem_closedBall,dist_zero_right]
    dsimp [R]
    linarith [hCenter i,le_abs_self B0,le_abs_self b.modelRadius]
  refine ⟨⟨{
    mu_pos := hmu
    Mb_nonneg := hMb.le
    radius_pos := by dsimp [R]; positivity
    buffer_pos := hbuffer
    region := U
    open_region := hOpenU
    native := fun nu i z hz => (hSubU nu i hz).2
    radius := hRadius
    buffered := hBallU
    noncritical := ?_
    first := ?_
    second := ?_ }⟩,hkappa,hKernel⟩
  · intro nu i z hz
    exact (hGeometry nu i z ((hSubU nu i (hBallU nu i z hz (mem_ball_self hbuffer))).2)).1
  · intro nu i z hz
    exact ((hGeometry nu i z (hSubU nu i hz).2).2 (hSubU nu i hz).1).1
  · intro nu i z hz
    exact ((hGeometry nu i z (hSubU nu i hz).2).2 (hSubU nu i hz).1).2

end OriginalCollars
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalCommonPrimaryGeometry.exists_counted_supply
#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_factory_primary_common_geometry
