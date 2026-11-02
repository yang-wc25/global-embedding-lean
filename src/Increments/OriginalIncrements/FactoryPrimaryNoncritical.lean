import OriginalIncrements.FactoryQuantitativeReferenceProfiles
import OriginalIncrements.OriginalPhysicalPhaseJets
import Repair.IncrementActualSignedTransport

/-!
# The literal factory phases have one original observing-host lower bound

The weighted covectors of the actual template family have the proved uniform
lower bound. The actual inverse original chart transition loses one factor
T. The resulting lower bound is identified with the spatial component of the
full native joint differential consumed by the counted grid producer.
No chosen adapted chart or inverse-function estimate is an input.
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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

/-- Exact lower bound after a genuine original spatial coordinate change. -/
theorem original_weighted_phase_observer_noncritical
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (xi : D →L[ℝ] ℝ) (weight mu T : ℝ) (hWeight : 1 ≤ weight)
    (hT : 0 < T) (hLower : mu ≤ ‖xi‖)
    (z : X) (hz : z ∈ (repairReferenceHostTransition observer owner).source)
    (hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm z.2))‖ ≤ T) :
    mu/T ≤ ‖fderiv ℝ (fun x : D => weight*xi (owner (observer.symm x))) z.2‖ := by
  obtain ⟨A,hA,hAi⟩ := repair_reference_transition_spatial_equiv observer owner hObserver hOwner z hz
  have hWeighted : mu ≤ ‖weight • xi‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans_le hWeight)]
    exact hLower.trans (by nlinarith [norm_nonneg xi])
  have h := increment_covector_transition_norm_lower A (weight • xi) mu T hT
    (by rwa [hAi]) hWeighted
  rw [repair_reference_actual_weighted_phase_differential observer owner hObserver hOwner xi weight z hz]
  rw [← hA]
  exact h

/-- Original fixed template and transition budgets supply noncriticality
in every original observing chart, before any adapted charts are selected. -/
theorem original_factory_primary_spatial_lower
    (b : RepairReferenceFactoryBudget m d N) (T : ℝ) (hT : 0 < T)
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
    (hWeight : ∀ nu, 1 ≤ weight nu)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (Parameter Spatial : ℕ → ℝ) (hTBound : Spatial 1 ≤ T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial),
    0 < b.covectorLower/T ∧
    ∀ nu i z, z ∈ actualOriginalPrimaryNativeOpen data nu i →
      b.covectorLower/T ≤ ‖fderiv ℝ (fun x : D => data.phase nu
        ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm x)) z.2‖ := by
  intro raw data hd transition
  have hEta := round4UniformTemplateCovectorLower_spec D V b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
  refine ⟨div_pos hEta.1 hT,?_⟩
  intro nu i z hz
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let observer := seed.atlas.chart i.1
  let owner := seed.atlas.chart a.1.1
  have hActive := (round3_prepared_native_primary_active data i nu hz).1
  have hOwn := repair_reference_original_family_owner_samples b seed hF Htensor S O K center family
    hseed outer hSample hSEval nu _ hActive
  have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp
    (round3_prepared_primary_native_subset data i nu hz)
  have hTransition : z ∈ (repairReferenceHostTransition («Ep» := Ep) observer owner).source :=
    ⟨mem_univ _,hOpen.1,hOwn.1⟩
  have hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm z.2))‖ ≤ T := by
    have hOwnSource : observer.symm z.2 ∈ owner.source := hOwn.1
    apply (increment_actual_spatial_transition_first data hd Parameter Spatial transition
      a.1.1 i.1 _ (owner.map_source hOwn.1) _ hOwn.2.1).trans hTBound
    change owner.symm (owner (observer.symm z.2)) ∈ observer.source
    rw [owner.left_inv hOwnSource]
    exact observer.map_target hOpen.1
  have hl : b.covectorLower ≤
      ‖(b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2‖ :=
    hEta.2 ((family a.1).pick a.2.1) a.2.2
  exact original_weighted_phase_observer_noncritical observer owner
    (hseed.atlas_smooth.chart_mem i.1) (hseed.atlas_smooth.chart_mem a.1.1)
    ((b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2)
    (weight nu) b.covectorLower T (hWeight nu) hT hl z hTransition hInverse

/-- The literal joint differential equals its fixed-parameter derivative on
the original primary open domain. This is the differential used by the grid. -/
theorem original_native_phase_spatial_fderiv
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z : X) (hz : z ∈ actualOriginalPrimaryNativeOpen Data nu i) :
    fderiv ℝ (fun x : D => Data.phase nu
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2 =
      (fderiv ℝ (OriginalIncrements.originalNativePrimaryPhase Data nu i) z).comp
        (ContinuousLinearMap.inr ℝ Ep D) := by
  have hsmooth := round3_actual_original_primary_native_phase_smooth Data hd hs nu i
  have hdiff : DifferentiableAt ℝ (OriginalIncrements.originalNativePrimaryPhase Data nu i) z :=
    (hsmooth.contDiffAt ((actualOriginalPrimaryNativeOpen_isOpen Data hd nu i).mem_nhds hz)).differentiableAt
      (by simp)
  exact (hdiff.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.original_weighted_phase_observer_noncritical
#print axioms GlobalEmbedding.Continuation.original_factory_primary_spatial_lower
#print axioms GlobalEmbedding.Continuation.original_native_phase_spatial_fderiv
