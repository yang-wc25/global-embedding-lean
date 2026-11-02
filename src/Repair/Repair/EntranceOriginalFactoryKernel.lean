import Repair.EntranceSpatialPrimaryBudget
import Repair.ReferenceOriginalLocalFactoryPrimaryKernel

/-! The original local factories, their actual operator-domain membership,
and the literal weighted phases manufacture the primary kernel input of
the same packet. The bound is numerical and precedes every adapted chart. -/

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
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

theorem repairEntrance_original_factory_kernel_inputs
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeight : ∀ nu, weight nu ≠ 0)
    (T : ℝ) (hT : 0 < T)
    (U : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    (∀ i, U i ⊆ actualOriginalNativeOpen data i) →
    (∀ nu i z, z ∈ U i →
      ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart a.1.1).symm)
        (seed.atlas.chart a.1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T) →
    RepairOriginalPrimaryKernelInputs data U (b.cover.restrictionReserve/T^2) := by
  intro raw data hUOpen hInverse
  refine ⟨?_⟩
  intro nu i z hz hPrimary
  have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp (hUOpen i hz)
  have hNative := round3_prepared_native_primary_mem data i nu z hOpen.1 hOpen.2.1
    ⟨hPrimary,hOpen.2.2,mem_univ _⟩
  exact repair_reference_original_family_primary_kernel b seed hF Htensor S O K center family
    hseed outer rho weight hWeight T hT nu i z hNative (hInverse nu i z hz hPrimary)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_original_factory_kernel_inputs
