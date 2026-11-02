import OriginalIncrements.FactoryPrimaryOriginalJets

/-!
# The actual factory supplies the common original primary geometry

All three numerical constants are fixed by the factory budget, the weight
cap, the original spatial transition bounds and the chosen common buffer.
The proof derives the lower bounds for the literal weighted template phase
and the original normal-Hessian restriction, and the full joint low jets.

The only domain sampling assumption concerns the spatial coordinate in the
unchanged original source norm domain. There is no construction-open-set
inclusion in the compact parameter sample and no adapted inverse premise.
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

theorem original_factory_primary_geometry_from_source_samples
    (b : RepairReferenceFactoryBudget m d N) (cap buffer T : ℝ)
    (hCap : 0 ≤ cap) (hBuffer : 0 ≤ buffer) (hT : 0 < T)
    (Parameter Spatial : ℕ → ℝ) (hSpatial : ∀ j, 0 ≤ Spatial j) (hTBound : Spatial 1 ≤ T)
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
    (hWeightLow : ∀ nu, 1 ≤ weight nu) (hWeightHigh : ∀ nu, |weight nu| ≤ cap)
    (hSourceSample : ∀ i z, z ∈ O i → z.2 ∈ seed.sourceNormDomain i.1) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    let mu := b.covectorLower/T
    let kappa := b.cover.restrictionReserve/T^2
    let Mb := originalFactoryPrimaryPhaseBudget cap b.cover.covectorBound buffer Spatial
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial),
      0 < mu ∧ 0 < kappa ∧ 0 < Mb ∧
      RepairOriginalPrimaryKernelInputs data (actualOriginalNativeOpen data) kappa ∧
      ∀ nu i z, z ∈ actualOriginalPrimaryNativeOpen data nu i →
        mu ≤ ‖(fderiv ℝ (OriginalIncrements.originalNativePrimaryPhase data nu i) z).comp
          (ContinuousLinearMap.inr ℝ Ep D)‖ ∧
        (z ∈ O i →
          ‖fderiv ℝ (OriginalIncrements.originalNativePrimaryPhase data nu i) z‖ ≤ Mb ∧
          buffer*‖iteratedFDeriv ℝ 2 (OriginalIncrements.originalNativePrimaryPhase data nu i) z‖ ≤ Mb) := by
  intro raw data mu kappa Mb hd hs transition
  have hEta := round4UniformTemplateCovectorLower_spec D V b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
  have hInverse := original_factory_reverse_transition_from_source_samples b T seed hF Htensor S O K
    center family hseed outer rho weight hSourceSample Parameter Spatial hTBound hd transition
  have hKernel : RepairOriginalPrimaryKernelInputs data (actualOriginalNativeOpen data) kappa := by
    apply repairEntrance_original_factory_kernel_inputs b seed hF Htensor S O K center family hseed outer
      rho weight (fun nu => ne_of_gt (zero_lt_one.trans_le (hWeightLow nu))) T hT
      (actualOriginalNativeOpen data) (fun _ => Subset.rfl)
    intro nu i z hz hActive
    have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp hz
    exact hInverse nu i z (round3_prepared_native_primary_mem data i nu z hOpen.1 hOpen.2.1
      ⟨hActive,hOpen.2.2,mem_univ _⟩)
  refine ⟨div_pos hEta.1 hT,div_pos b.cover.restrictionReserve_pos (sq_pos_of_pos hT),
    originalFactoryPrimaryPhaseBudget_pos cap b.cover.covectorBound buffer Spatial
      hCap b.cover.covectorBound_pos.le hBuffer hSpatial,hKernel,?_⟩
  intro nu i z hz
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let observer := seed.atlas.chart i.1
  let owner := seed.atlas.chart a.1.1
  have hActive := (round3_prepared_native_primary_active data i nu hz).1
  have hOwn := original_factory_owner_construction_point b seed hF Htensor S O K center family
    hseed outer nu _ hActive
  have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp
    (round3_prepared_primary_native_subset data i nu hz)
  have hTransition : z ∈ (repairReferenceHostTransition («Ep» := Ep) observer owner).source :=
    ⟨mem_univ _,hOpen.1,hOwn.1.2⟩
  have hLower := original_weighted_phase_observer_noncritical observer owner
    (hseed.atlas_smooth.chart_mem i.1) (hseed.atlas_smooth.chart_mem a.1.1)
    ((b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2)
    (weight nu) b.covectorLower T (hWeightLow nu) hT
    (hEta.2 ((family a.1).pick a.2.1) a.2.2) z hTransition (hInverse nu i z hz)
  constructor
  · rw [← original_native_phase_spatial_fderiv data hd hs nu i z hz]
    exact hLower
  · intro hzO
    have hJets := original_factory_primary_native_positive_jets b cap hCap seed hF Htensor S O K
      center family hseed outer rho weight hWeightHigh hSourceSample Parameter Spatial hd transition
      nu i z hzO hz
    exact original_native_phase_low_budget_from_positive_jets
      (OriginalIncrements.originalNativePrimaryPhase data nu i) z cap b.cover.covectorBound buffer Spatial
      hCap b.cover.covectorBound_pos.le hBuffer hSpatial (hJets 1 le_rfl) (hJets 2 (by omega))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.original_factory_primary_geometry_from_source_samples
