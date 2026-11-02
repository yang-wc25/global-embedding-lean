import OriginalIncrements.QuantitativeReferenceProfiles
import Repair.EntranceOriginalFactoryKernel
import Repair.ReferenceOriginalLocalFactoryDomains
import Repair.IncrementRegionTransitionBudget

/-!
# Actual original templates manufacture the quantitative grid reference

The literal weighted factory phases produce the original kernel inequality;
that output is transported through the retained restrictions of the same
budgeted grid packet. The public input contains the original reverse spatial
transition bound, and no adapted inverse estimate, kernel lower bound, or
transverse reserve. The resulting cT has the displayed numerical expression
in the template budget, reverse transition bound and fixed phase-jet budget.
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
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

theorem original_factory_budgeted_reference_profiles
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
    (T Mb : ℝ) (hT : 0 < T) (hMb : 0 ≤ Mb) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hp : IncrementsOriginalPhaseConditions data hd hs)
      (hImm : IncrementsOriginalSliceImmersionInputs data)
      (theta : (Fin data.atlas.count × Fin data.parameterCount) → P × M → ℝ)
      (budgeted : OriginalIncrements.OriginalBudgetedPrimarySupply data theta),
    (∀ nu i a y, y ∈ tsupport (budgeted.packet.piece nu i a).cutoff →
      y.2 ∈ data.atlas.inner (budgeted.packet.piece nu i a).host) →
    (∀ nu i, budgeted.Mb nu i ≤ Mb) →
    (∀ nu i z, z ∈ actualOriginalNativeOpen data i →
      ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart a.1.1).symm)
        (seed.atlas.chart a.1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T) →
    ∃ geometry : RestrictedReferenceGeometry data hd hs theta budgeted.packet,
      geometry.cT =
        ((b.cover.restrictionReserve/T^2)/
          ((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2 := by
  intro raw data hd hs hp hImm theta budgeted hInner hMbBound hInverse
  have kernel := repairEntrance_original_factory_kernel_inputs b seed hF Htensor S O K center
    family hseed outer rho weight hWeight T hT (actualOriginalNativeOpen data)
    (fun _ => subset_rfl) hInverse
  exact original_budgeted_reference_profiles_from_kernel data hd hs hp hImm theta budgeted
    hInner Mb (b.cover.restrictionReserve/T^2) hMb
    (div_pos b.cover.restrictionReserve_pos (sq_pos_of_pos hT)) hMbBound kernel

theorem original_factory_reference_profiles_from_original_transitions
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
    (T Mb : ℝ) (hT : 0 < T) (hMb : 0 ≤ Mb)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (Parameter Spatial : ℕ → ℝ) (hTBound : Spatial 1 ≤ T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hp : IncrementsOriginalPhaseConditions data hd hs)
      (hImm : IncrementsOriginalSliceImmersionInputs data)
      (theta : (Fin data.atlas.count × Fin data.parameterCount) → P × M → ℝ)
      (budgeted : OriginalIncrements.OriginalBudgetedPrimarySupply data theta),
    (∀ nu i a y, y ∈ tsupport (budgeted.packet.piece nu i a).cutoff →
      y.2 ∈ data.atlas.inner (budgeted.packet.piece nu i a).host) →
    (∀ nu i, budgeted.Mb nu i ≤ Mb) →
    RepairOriginalTransitionBudgets data Parameter Spatial →
    ∃ geometry : RestrictedReferenceGeometry data hd hs theta budgeted.packet,
      geometry.cT =
        ((b.cover.restrictionReserve/T^2)/
          ((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2 := by
  intro raw data hd hs hp hImm theta budgeted hInner hMbBound transition
  let index := fun nu => repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let owner := fun nu => seed.atlas.chart (index nu).1.1
  have hOwn (nu) (z : P × M) (hz : z ∈ data.primaryDomain nu) :=
    repair_reference_original_family_owner_samples b seed hF Htensor S O K center family
      hseed outer hSample hSEval nu z hz
  have hReverse (nu) (i) (z : X) (hz : z ∈ actualOriginalNativeOpen data i)
      (hActive : ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu) :
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart (index nu).1.1).symm)
        (seed.atlas.chart (index nu).1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T := by
    have hOwn' := hOwn nu _ hActive
    have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp hz
    apply (increment_actual_spatial_transition_first data hd Parameter Spatial transition
      (index nu).1.1 i.1 _ ((owner nu).map_source hOwn'.1) _ hOwn'.2.1).trans hTBound
    change (owner nu).symm (owner nu ((data.atlas.chart i.1).symm z.2)) ∈ (data.atlas.chart i.1).source
    rw [(owner nu).left_inv hOwn'.1]
    exact (data.atlas.chart i.1).map_target hOpen.1
  exact original_factory_budgeted_reference_profiles b seed hF Htensor S O K center family
    hseed outer rho weight hWeight T Mb hT hMb hd hs hp hImm theta budgeted hInner hMbBound hReverse

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.original_factory_budgeted_reference_profiles

#print axioms GlobalEmbedding.Continuation.original_factory_reference_profiles_from_original_transitions
