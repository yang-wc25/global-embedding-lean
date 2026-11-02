import OriginalIncrements.FactoryPrimaryNoncritical
import Repair.IncrementGivenPhaseJets

/-!
# Original-domain phase geometry for the literal factory datum

Only the original spatial norm domain is needed for the template phases.
The construction domain is not required to lie over the compact parameter
sample. The source-domain inclusion below is separate from the parameter
sample and is preserved even when that sample has boundary.

The actual weighted linear phases have full joint first and second jets
controlled by the original spatial transition profile. The original reverse
transition also supplies the common noncritical lower bound. No adapted
map, grid, cutoff derivative or completed phase norm is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

def originalFactoryPrimaryPhaseBudget (cap covectorBound buffer : ℝ)
    (Spatial : ℕ → ℝ) : ℝ :=
  1+cap*covectorBound*(Spatial 1+buffer*Spatial 2)

theorem originalFactoryPrimaryPhaseBudget_pos (cap covectorBound buffer : ℝ)
    (Spatial : ℕ → ℝ) (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound)
    (hBuffer : 0 ≤ buffer) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    0 < originalFactoryPrimaryPhaseBudget cap covectorBound buffer Spatial := by
  unfold originalFactoryPrimaryPhaseBudget
  have hOne := hSpatial 1
  have hTwo := hSpatial 2
  positivity

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

/-- Positive native joint phase jets use only original source samples. -/
theorem original_native_literal_phase_positive_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (owner : Fin Data.atlas.count)
    (xi : D →L[ℝ] ℝ) (weight cap covectorBound : ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound)
    (hWeight : |weight| ≤ cap) (hXi : ‖xi‖ ≤ covectorBound)
    (hPhase : Data.phase nu = fun z => weight*xi (Data.atlas.chart owner z.2))
    (hSource : ∀ z ∈ Data.primaryDomain nu, z.2 ∈ (Data.atlas.chart owner).source)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hz : z ∈ actualOriginalPrimaryNativeOpen Data nu i)
    (hSample : z.2 ∈ Data.sourceNormDomain i.1)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (OriginalIncrements.originalNativePrimaryPhase Data nu i) z‖ ≤
      cap*covectorBound*Spatial j := by
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (Data.atlas.chart owner)
  let L := xi.comp (ContinuousLinearMap.snd ℝ Ep D)
  have hActive := (round3_prepared_native_primary_active Data i nu hz).1
  have hOpen := (round3Parameter_originalNativeOpen_iff Data i z).mp
    (round3_prepared_primary_native_subset Data i nu hz)
  have hS : z ∈ S.source := ⟨mem_univ _,hOpen.1,hSource _ hActive⟩
  have hs := (repair_reference_host_transition_smooth («Ep» := Ep) (Data.atlas.chart i.1)
    (Data.atlas.chart owner) (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem owner)).1
  have hL : ‖L‖ ≤ covectorBound := (xi.opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg xi) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hXi)
  have h := increment_given_positive_linear_jets L S z (hs.contDiffAt (S.open_source.mem_nhds hS))
    weight cap covectorBound (Spatial j) hWeight hCap hL hCovector j
    (transition.spatial i.1 owner j hj z hSample hS)
  have he : OriginalIncrements.originalNativePrimaryPhase Data nu i = fun y => weight*L (S y) := by
    funext y
    simp only [OriginalIncrements.originalNativePrimaryPhase,hPhase]
    rfl
  rwa [he]

/-- The primitive normal carrier lies in its literal owner's construction
domain. No parameter sample or evaluation inclusion is involved. -/
theorem original_factory_owner_construction_point
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) (z : P × M)
    (hz : z ∈ (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryDomain nu) :
    let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
    let q := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
    z ∈ q.source ∧ q z ∈ O a.1 := by
  intro a q
  change z ∈ q.source ∩ q ⁻¹' round4NormalCutoffCarrier
    ((family a.1).charts a.2.1 a.2.2).chart a.2.1.val b.normalRadius at hz
  exact ⟨hz.1,((family a.1).charts a.2.1 a.2.2).source_domain hz.2.1⟩

/-- Source-domain sampling alone supplies the original reverse transition
at every actual primary point. -/
theorem original_factory_reverse_transition_from_source_samples
    (b : RepairReferenceFactoryBudget m d N) (T : ℝ)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hSourceSample : ∀ i z, z ∈ O i → z.2 ∈ seed.sourceNormDomain i.1)
    (Parameter Spatial : ℕ → ℝ) (hTBound : Spatial 1 ≤ T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (nu : Fin data.primaryCount) (i : Fin data.atlas.count × Fin data.parameterCount)
      (z : X), z ∈ actualOriginalPrimaryNativeOpen data nu i →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart a.1.1).symm)
        (seed.atlas.chart a.1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T := by
  intro raw data hd transition nu i z hz a
  let observer := seed.atlas.chart i.1
  let owner := seed.atlas.chart a.1.1
  have hActive := (round3_prepared_native_primary_active data i nu hz).1
  have hOwn := original_factory_owner_construction_point b seed hF Htensor S O K center family
    hseed outer nu _ hActive
  have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp
    (round3_prepared_primary_native_subset data i nu hz)
  have hOwnSource : observer.symm z.2 ∈ owner.source := hOwn.1.2
  have hOwnSample : owner (observer.symm z.2) ∈ data.sourceNormDomain a.1.1 :=
    hSourceSample a.1 _ hOwn.2
  apply (increment_actual_spatial_transition_first data hd Parameter Spatial transition
    a.1.1 i.1 _ (owner.map_source hOwnSource) _ hOwnSample).trans hTBound
  change owner.symm (owner (observer.symm z.2)) ∈ observer.source
  rw [owner.left_inv hOwnSource]
  exact observer.map_target hOpen.1

/-- The same literal factory phases, with the common covector cap, supply
all positive full native jets on each original construction domain. -/
theorem original_factory_primary_native_positive_jets
    (b : RepairReferenceFactoryBudget m d N) (cap : ℝ) (hCap : 0 ≤ cap)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeight : ∀ nu, |weight nu| ≤ cap)
    (hSourceSample : ∀ i z, z ∈ O i → z.2 ∈ seed.sourceNormDomain i.1)
    (Parameter Spatial : ℕ → ℝ) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (nu : Fin data.primaryCount) (i : Fin data.atlas.count × Fin data.parameterCount)
      (z : X), z ∈ O i → z ∈ actualOriginalPrimaryNativeOpen data nu i →
      ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ j (OriginalIncrements.originalNativePrimaryPhase data nu i) z‖ ≤
          cap*b.cover.covectorBound*Spatial j := by
  intro raw data hd transition nu i z hzO hz j hj
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let xi := (b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2
  apply original_native_literal_phase_positive_jets data hd nu a.1.1 xi (weight nu)
    cap b.cover.covectorBound hCap b.cover.covectorBound_pos.le (hWeight nu)
    ((b.cover.bounds ((family a.1).pick a.2.1)).2.2.2.2 a.2.2) rfl
    (fun y hy => (original_factory_owner_construction_point b seed hF Htensor S O K center family
      hseed outer nu y hy).1.2) Parameter Spatial transition i z hz
    (hSourceSample i z hzO) j hj

/-- One numerical low budget controls the actual full first jet and the
buffer-weighted second jet used by the counted phase grid. -/
theorem original_native_phase_low_budget_from_positive_jets
    (psi : X → ℝ) (z : X) (cap covectorBound buffer : ℝ) (Spatial : ℕ → ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hBuffer : 0 ≤ buffer)
    (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hFirst : ‖iteratedFDeriv ℝ 1 psi z‖ ≤ cap*covectorBound*Spatial 1)
    (hSecond : ‖iteratedFDeriv ℝ 2 psi z‖ ≤ cap*covectorBound*Spatial 2) :
    ‖fderiv ℝ psi z‖ ≤ originalFactoryPrimaryPhaseBudget cap covectorBound buffer Spatial ∧
      buffer*‖iteratedFDeriv ℝ 2 psi z‖ ≤ originalFactoryPrimaryPhaseBudget cap covectorBound buffer Spatial := by
  rw [norm_iteratedFDeriv_one] at hFirst
  have hC : 0 ≤ cap*covectorBound := mul_nonneg hCap hCovector
  have h1 : 0 ≤ cap*covectorBound*Spatial 1 := mul_nonneg hC (hSpatial 1)
  have h2 : 0 ≤ buffer*(cap*covectorBound*Spatial 2) :=
    mul_nonneg hBuffer (mul_nonneg hC (hSpatial 2))
  have hSecond' := mul_le_mul_of_nonneg_left hSecond hBuffer
  unfold originalFactoryPrimaryPhaseBudget
  constructor <;> nlinarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.original_native_literal_phase_positive_jets
#print axioms GlobalEmbedding.Continuation.original_factory_owner_construction_point
#print axioms GlobalEmbedding.Continuation.original_factory_reverse_transition_from_source_samples
#print axioms GlobalEmbedding.Continuation.original_factory_primary_native_positive_jets
#print axioms GlobalEmbedding.Continuation.original_native_phase_low_budget_from_positive_jets
