import OriginalCollars.OriginalObserverCutoffSupply

/-!
# Exact finite cutoff profiles on every original observation domain

Every cutoff is the one in the original budgeted primary packet.  Its
explicit raw-parent/grid profile is transferred only on actual support,
and the zero germ treats every other original observation point.  Reference
conditioning preserves these physical functions, so the same profile works
for the conditioned mean packet without any new derivative hypothesis.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance originalObserverProductChart : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P D M
private local instance originalObserverProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

/-- The complete original-observer cutoff estimate is supplied by the
explicit finite formula, for every order and all later scales at once. -/
theorem original_primary_observer_cutoff_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
    (hOne : EqOn psi 1 V)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (supply : OriginalBudgetedPrimarySupply Data theta)
      (_hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (_hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)),
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta supply.packet
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ nu beta observer j z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      ell^j * ‖iteratedFDeriv ℝ j (fun y : X => g.eta nu beta
        ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤
        originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j := by
  intro theta supply hCompact hSmooth g ell hell hell1 nu beta observer j z hz
  let q := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  have hq (i) : q i ∈ maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2)
      (hd.atlas_smooth.chart_mem i.1)
  let rho := g.eta nu beta
  have hGeometry := round3ParameterWholePrimaryFamily_cutoff_geometry
    Data hd hs hn theta supply.packet nu beta
  have hRho : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ rho := by
    rw [modelWithCornersSelf_prod]
    exact hGeometry.1
  have hRhoSupport : tsupport rho ⊆ (q beta.1).source := by
    intro y hy
    have hh := CollarCompletion.original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi beta.1 (hGeometry.2.2.1 hy)
    have hp := B.inner_subset beta.1.2 hh.1
    rw [hChart] at hp
    exact ⟨hp,Data.atlas.inner_subset beta.1.1 hh.2⟩
  have hEval := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hez : z ∈ (q observer).target :=
    ⟨hd.parameter_norm_subset observer.2 hEval.2.1,hd.source_norm_subset observer.1 hEval.1⟩
  let T := fun k => max (Parameter k) (Spatial k)
  have hT : ∀ k, 0 ≤ T k := fun k => (hParameter k).trans (le_max_left _ _)
  let H := originalParentGridHostCutoffProfile m d (supply.mu nu beta.1) (supply.Mb nu beta.1)
    (supply.buffer nu beta.1) BS TS BP TP Ds Dp j
  have hH : 0 ≤ H := originalParentGridHostCutoffProfile_nonneg m d _ _ _
    (supply.mu_pos nu beta.1) (supply.Mb_nonneg nu beta.1) (supply.buffer_pos nu beta.1)
    BS TS BP TP hBS hTS hBP hTP Ds Dp j
  have hHostJets : (q observer).symm z ∈ tsupport rho → ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k (rho ∘ (q beta.1).symm) ((q beta.1) ((q observer).symm z))‖ ≤ H := by
    intro hActive k hkj
    have hPhysical := hRhoSupport hActive
    have hTarget := (q beta.1).map_source hPhysical
    have hK : (Data.parameterChart beta.1.2).symm
        ((q beta.1) ((q observer).symm z)).1 ∈ Data.parameterSet := by
      change (Data.parameterChart beta.1.2).symm
        ((Data.parameterChart beta.1.2) ((Data.parameterChart observer.2).symm z.1)) ∈ Data.parameterSet
      have hPhysicalP : (Data.parameterChart observer.2).symm z.1 ∈
          (Data.parameterChart beta.1.2).source := hPhysical.1
      rw [(Data.parameterChart beta.1.2).left_inv hPhysicalP]
      exact hEval.2.2
    exact original_primary_family_cutoff_host_prefix Data hd hs hn BS TS BP TP
      hBS hTS hBP hTP Ds Dp B hChart RS RP psi V hV hKV hOne supply hCompact hSmooth
      nu beta j k hkj ((q beta.1) ((q observer).symm z)) hTarget.1 hTarget.2 hK
  have hTransitionJets : (q observer).symm z ∈ tsupport rho → ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k ((q beta.1) ∘ (q observer).symm) z‖ ≤ T k := by
    intro hActive k hk _
    have hPhysical := hRhoSupport hActive
    have hpair : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
        incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
      (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
    have hp := congrArg Prod.fst hpair
    have hx := congrArg Prod.snd hpair
    dsimp only at hp hx
    have hSample : parameterTensorModelEquiv (m+1) d z ∈
        actualOriginalGivenTransitionSample Data (observer,beta.1) := by
      refine ⟨hz,hz.1,?_⟩
      change (Data.parameterChart observer.2).symm
          (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z)) ∈
          (Data.parameterChart beta.1.2).source ∧
        (Data.atlas.chart observer.1).symm
          (incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) ∈
          (Data.atlas.chart beta.1.1).source
      rw [hp,hx]
      exact hPhysical
    have h := (increment_given_actual_native_transition_jets Data hd Parameter Spatial transition
      (observer,beta.1) (parameterTensorModelEquiv (m+1) d z) hSample k hk).2
    have hFun : (q beta.1) ∘ (q observer).symm = (fun w : X =>
        (Data.parameterChart beta.1.2 ((Data.parameterChart observer.2).symm w.1),
          Data.atlas.chart beta.1.1 ((Data.atlas.chart observer.1).symm w.2))) := by
      funext w
      rfl
    rw [hFun]
    simpa only [ContinuousLinearEquiv.symm_apply_apply,T] using h
  have hActual := cutoff_observer_bound_from_explicit_host_jets
    (q beta.1) (q observer) (hq beta.1) (hq observer) rho hRho hRhoSupport T hT
    j H hH z hez hHostJets hTransitionJets
  have hFinite := round3PreparedFiniteMaximum_bound
    (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
      actualFastChartTransferCost T j * originalParentGridHostCutoffProfile m d
        (supply.mu a.1 a.2) (supply.Mb a.1 a.2) (supply.buffer a.1 a.2) BS TS BP TP Ds Dp j)
    (nu,beta.1)
  exact ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hActual).trans hFinite

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_primary_observer_cutoff_budget
