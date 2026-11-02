import Repair.ReferenceOriginalLocalFactoryPhases
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
private local instance familyKernelRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance familyKernelSquareNormed {E : Type*}
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
theorem repair_reference_original_family_primary_kernel
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeight : ∀ nu, weight nu ≠ 0)
    (T : ℝ) (hT : 0 < T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (nu : Fin data.primaryCount) (i : Fin seed.atlas.count × Fin seed.parameterCount)
      (z : X), z ∈ actualOriginalPrimaryNativeOpen data nu i →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart a.1.1).symm)
        (seed.atlas.chart a.1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T →
      ∀ v, (b.cover.restrictionReserve/T^2)*‖v‖ ≤
        ‖covectorRestriction
          (round4ActualPhaseOperatorInChart
            (fun p x => data.F ((data.parameterChart i.2).symm p,x))
            (fun _ => data.atlas.chart i.1) z)
          (fderiv ℝ (fun x : D => data.phase nu
            ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm x)) z.2) v‖ := by
  intro raw data nu i z hz a hInverse
  let observer := seed.atlas.chart i.1
  let owner := seed.atlas.chart a.1.1
  let p := (seed.parameterChart i.2).symm z.1
  let F := fun x => seed.F0 (p,x)
  have hActive := (round3_prepared_native_primary_active data i nu hz).1
  have hOperator := repair_reference_original_family_operator b seed hF Htensor S O K center family
    hseed outer nu (p,observer.symm z.2) hActive
  have hObs := (round3Parameter_originalNativeOpen_iff data i z).mp
    (round3_prepared_primary_native_subset data i nu hz)
  have hTransition : (0,z.2) ∈ (repairReferenceHostTransition («Ep» := ℝ) observer owner).source :=
    ⟨mem_univ _,hObs.1,hOperator.1⟩
  have hWorld : repairReferenceHostTransition («Ep» := ℝ) observer owner (0,z.2) ∈
      (univ : Set ℝ) ×ˢ owner.target := ⟨mem_univ _,owner.map_source hOperator.1⟩
  have hTemplate : round4ActualPhaseOperatorInChart (fun (_ : ℝ) => F) (fun _ => owner)
      (repairReferenceHostTransition («Ep» := ℝ) observer owner (0,z.2)) ∈
      (b.cover.template ((family a.1).pick a.2.1)).operatorDomain := hOperator.2.2
  have h := repair_reference_actual_primary_kernel_reserve b.cover T hT
    (fun (_ : ℝ) => F) (fun _ => hF p) observer owner
    (hseed.atlas_smooth.chart_mem i.1) (hseed.atlas_smooth.chart_mem a.1.1)
    (univ ×ˢ owner.target) (isOpen_univ.prod owner.open_target)
    (repair_reference_slice_joint_smooth F (hF p) owner (hseed.atlas_smooth.chart_mem a.1.1))
    (0,z.2) hTransition hWorld hInverse ((family a.1).pick a.2.1) a.2.2 hTemplate
    (weight nu) (hWeight nu)
  exact h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_primary_kernel
