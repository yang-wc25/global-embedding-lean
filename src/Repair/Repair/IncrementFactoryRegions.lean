import Repair.IncrementFactoryNumericalBudgets
import Repair.IncrementRegionJointTransition

/-! Every actual factory secondary region is produced here from the same
literal weighted data, the original collar and original transition
budgets. All phase derivatives and kernel reserves are outputs. -/

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
theorem increment_actual_factory_signed_regions
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
    (B0 Bs : ℝ) (hCenter : ∀ i, ‖center i‖ ≤ B0)
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
      (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial) (hFirst : Spatial 1 ≤ T),
    ∀ r i, Nonempty (IncrementActualSignedRegion data i r
      ((data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (data.parameterChart i.2) (theta i))
      (incrementFactorySignedMu b T) b.modelRadius (incrementFactorySignedBuffer b Parameter Spatial)
      (incrementFactorySignedCoordinate b B0 Parameter Spatial) (incrementFactorySignedKernel b T)
      (incrementFactorySignedPhaseProfile b T B0 Bs labelBound Parameter Spatial)) := by
  intro raw weight data hd hs Parameter Spatial hParameter transition hFirst
  let Joint := incrementFactoryJointProfile Parameter Spatial
  have hJoint : ∀ j, 0 ≤ Joint j := fun j => (hParameter j).trans (le_max_left _ _)
  have hEval (i) (z) (hz : z ∈ O i) : parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
        data.parameterNormDomain data.parameterSet i := hSEval i (hSample i z hz)
  have hOOpen (i) : O i ⊆ actualOriginalNativeOpen data i := by
    intro z hz
    have he := (actual_original_native_evaluation_iff data hd i z).mp (hEval i z hz)
    exact (round3Parameter_originalNativeOpen_iff data i z).mpr
      ⟨hd.source_norm_subset i.1 he.1,hd.parameter_norm_subset i.2 he.2.1,hd.parameter_subset he.2.2⟩
  have hTransition : ∀ nu i z, z ∈ O i → ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ Joint j := by
    intro nu i z hz j hj a owner observer hOwner
    exact increment_actual_original_joint_transition_jets data hd Parameter Spatial transition
      i a.1 z (hEval i z hz) hOwner j hj
  have hGeom := repair_reference_original_factory_interaction_geometry b seed hF Htensor S O K center family
    hseed (fun i y hy => (hSEval i hy).1) hSample outer theta hCompact hSmooth hThetaSource hO hK hBuffer
    B0 hCenter Joint hJoint hTransition rho weight hd hOOpen hInner hEval
  obtain ⟨literal⟩ := increment_actual_factory_literal_phase_data b seed hF Htensor S O K center family
    hseed outer hSample hSEval rho T labelBound label hLabel hProper
  intro r i
  obtain ⟨geometry⟩ := hGeom r i
  exact increment_actual_complete_signed_region data hd hs b.cover b.operatorBound T hT labelBound literal
    i r (round3ParameterNativeParent (data.parameterChart i.2) (theta i))
    b.modelRadius (incrementFactorySignedBuffer b Parameter Spatial)
    (incrementFactorySignedCoordinate b B0 Parameter Spatial) Bs
    (incrementFactorySignedBuffer_pos b Parameter Spatial hParameter) geometry hSourceValue
    Parameter Spatial transition hFirst

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_factory_signed_regions
