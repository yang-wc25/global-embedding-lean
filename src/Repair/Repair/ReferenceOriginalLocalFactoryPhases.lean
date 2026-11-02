import Repair.ReferenceOriginalLocalFactoryGlobal
import Repair.ReferenceNativePhaseConditions

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
private local instance familyPhaseRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance familyPhaseSquareNormed {E : Type*}
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
theorem repair_reference_original_family_operator
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) (z : P × M)
    (hz : z ∈ (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryDomain nu) :
    let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
    z.2 ∈ (seed.atlas.chart a.1.1).source ∧
      ‖repairReferenceSliceOperator (fun x => seed.F0 (z.1,x)) (seed.atlas.chart a.1.1)
        (seed.atlas.chart a.1.1 z.2)‖ ≤ b.operatorBound ∧
      repairReferenceSliceOperator (fun x => seed.F0 (z.1,x)) (seed.atlas.chart a.1.1)
        (seed.atlas.chart a.1.1 z.2) ∈ (b.cover.template ((family a.1).pick a.2.1)).operatorDomain := by
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  change z ∈ ((seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)).source ∩
    ((seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)) ⁻¹'
      round4NormalCutoffCarrier ((family a.1).charts a.2.1 a.2.2).chart a.2.1.val b.normalRadius at hz
  have heq : repairReferenceSliceOperator (fun x => seed.F0 (z.1,x)) (seed.atlas.chart a.1.1)
      (seed.atlas.chart a.1.1 z.2) =
      (repairReferenceFactoryField seed Htensor a.1
        (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2)).1 := by
    change _ = repairReferenceSliceOperator
      (fun x => seed.F0 ((seed.parameterChart a.1.2).symm (seed.parameterChart a.1.2 z.1),x))
      (seed.atlas.chart a.1.1) (seed.atlas.chart a.1.1 z.2)
    rw [(seed.parameterChart a.1.2).left_inv hz.1.1]
  refine ⟨hz.1.2,?_,?_⟩
  · rw [heq]
    exact (family a.1).operator_bound _ (((family a.1).charts a.2.1 a.2.2).source_domain hz.2.1)
  · rw [heq]
    exact ((family a.1).charts a.2.1 a.2.2).operator_domain _ hz.2.1

include hF Htensor O K center in
theorem repair_reference_original_family_relative_outer
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) (z : P × M)
    (hz : z ∈ incrementsOriginalRelativeCutoffSupport
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) nu) :
    z ∈ tsupport (outer (repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu).1) := by
  obtain ⟨w,hw,rfl⟩ := hz
  exact tsupport_comp_subset_preimage _ continuous_subtype_val (tsupport_mul_subset_left hw)

include hF Htensor O K center in
theorem repair_reference_original_family_phase_conditions
    (rho transitionBound : ℝ) (hT : 0 ≤ transitionBound)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu mu, nu ≠ mu →
      (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
       tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
        label nu ≠ label mu)
    (hTransition : ∀ i j z, z ∈ tsupport (outer i) ∩ tsupport (outer j) →
      ‖fderiv ℝ (seed.atlas.chart j.1 ∘ (seed.atlas.chart i.1).symm) (seed.atlas.chart i.1 z.2)‖ ≤ transitionBound) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferencePositiveData raw rho
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound transitionBound ^ label nu
      IncrementsOriginalPhaseConditions (repairReferenceWeightedData data weight)
        (repairReferenceWeightedDomain data weight hd) (repairReferenceWeightedSmooth data weight hs) := by
  intro raw data hd hs weight
  let index := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  apply repair_reference_native_phase_conditions b.cover b.operatorBound transitionBound hT data hd hs
    (fun nu => seed.atlas.chart (index nu).1.1)
    (fun nu => hseed.atlas_smooth.chart_mem (index nu).1.1)
    (fun nu => (family (index nu).1).pick (index nu).2.1) (fun nu => (index nu).2.2) label
    (fun _ => rfl)
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
    exact hTransition (index nu).1 (index mu).1 z
      ⟨repair_reference_original_family_relative_outer b seed hF Htensor S O K center family hseed outer nu z hz.1,
        repair_reference_original_family_relative_outer b seed hF Htensor S O K center family hseed outer mu z hz.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_operator
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_phase_conditions
