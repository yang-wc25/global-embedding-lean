import Repair.ReferenceOriginalLocalFactoryDomains
import Repair.EndpointSpatialTransitionJets
import Repair.ReferenceNativePhaseConditions
import Repair.ReferenceActualKernelTransport
import Probes.Round3PreparedOriginalDomains
import Probes.Round3ParameterCrossNativeData

/-! The actual factory supplies every template-membership and operator-bound
input needed by the common signed hierarchy. The resulting theorem concerns
the literal original native data, including all cross-host signed phases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance familyNativePhaseRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance familyNativePhaseSquareNormed {E : Type*}
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
theorem repair_reference_original_factory_native_phases
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (rho T : ℝ) (hT : 0 ≤ T)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu mu, nu ≠ mu →
      (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
       tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
        label nu ≠ label mu)
    (Parameter Spatial : ℕ → ℝ) (hSpatial : Spatial 1 ≤ T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferencePositiveData raw rho
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      RepairOriginalTransitionBudgets data Parameter Spatial →
      let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound T^label nu
      IncrementsOriginalPhaseConditions (repairReferenceWeightedData data weight)
        (repairReferenceWeightedDomain data weight hd) (repairReferenceWeightedSmooth data weight hs) := by
  intro raw data hd hs transitions weight
  let index := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  apply repair_reference_native_phase_conditions b.cover b.operatorBound T hT data hd hs
    (fun nu => seed.atlas.chart (index nu).1.1)
    (fun nu => hseed.atlas_smooth.chart_mem (index nu).1.1)
    (fun nu => (family (index nu).1).pick (index nu).2.1) (fun nu => (index nu).2.2)
    label (fun _ => rfl)
    (fun nu z hz => (repair_reference_original_family_operator b seed hF Htensor S O K center family
      hseed outer nu z hz.1).1)
    (fun nu z hz => (repair_reference_original_family_operator b seed hF Htensor S O K center family
      hseed outer nu z hz.1).2)
  · intro nu mu hne z hz
    apply hLabel nu mu hne
    refine ⟨z,?_,?_⟩
    · obtain ⟨w,hw,rfl⟩ := hz.1
      exact tsupport_comp_subset_preimage _ continuous_subtype_val hw
    · obtain ⟨w,hw,rfl⟩ := hz.2
      exact tsupport_comp_subset_preimage _ continuous_subtype_val hw
  · intro nu mu z hz
    have hNu := repair_reference_original_family_owner_samples b seed hF Htensor S O K center family
      hseed outer hSample hSEval nu z (hd.cutoff_support_local nu hz.1)
    have hMu := repair_reference_original_family_owner_samples b seed hF Htensor S O K center family
      hseed outer hSample hSEval mu z (hd.cutoff_support_local mu hz.2)
    have hOverlap : seed.atlas.chart (index nu).1.1 z.2 ∈
        ((seed.atlas.chart (index nu).1.1).symm.trans (seed.atlas.chart (index mu).1.1)).source := by
      refine ⟨(seed.atlas.chart (index nu).1.1).map_source hNu.1,?_⟩
      change (seed.atlas.chart (index nu).1.1).symm (seed.atlas.chart (index nu).1.1 z.2) ∈
        (seed.atlas.chart (index mu).1.1).source
      rw [(seed.atlas.chart (index nu).1.1).left_inv hNu.1]
      exact hMu.1
    have hj := repair_original_spatial_transition_jets data hd Parameter Spatial transitions
      (index nu).1.1 (index mu).1.1 (seed.atlas.chart (index nu).1.1 z.2) hNu.2.1 hOverlap 1 le_rfl
    rw [norm_iteratedFDeriv_one] at hj
    exact hj.trans hSpatial

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_factory_native_phases
