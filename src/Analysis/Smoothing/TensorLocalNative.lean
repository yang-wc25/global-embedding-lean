import Smoothing.TensorLocalWeighted

/-!
# Native local parameter tensor geometry and the original coordinate norms

No parameter cover of all P is assumed. The true source tangent frame is
the spatial block of the real joint Jacobian. Original source-first tensor
coordinates and their cumulative chart maximum are retained exactly, with
the actual joint sampling buffer contained in the original independent ones.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper
  GlobalEmbedding.Continuation Function Set Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Offline
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance tensorLocalNativeChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance tensorLocalNativeManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

theorem tensorLocalNativeFrame_eq_fderiv
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (p i : Fin A.count × Fin pcount) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ tensorLocalChartOverlap (parameterLocalProductFamily A B) p i) :
    tensorLocalFrameTransition (parameterLocalProductFamily A B) (tensorLocalParameterFrame A B hA) p i a r y =
      parameterTensorJacobianEntryCLM a r
        (fderiv ℝ ((parameterLocalProductFamily A B).chart i ∘
          ((parameterLocalProductFamily A B).chart p).symm) y) := by
  have hyp : y.1 ∈ tensorLocalChartOverlap B p.2 i.2 := ⟨hy.1.1,hy.2.1⟩
  have hys : y.2 ∈ bufferedChartOverlap A p.1 i.1 := ⟨hy.1.2,hy.2.2⟩
  rw [tensorLocalParameterFrameTransition_eq_source]
  change tensorFrameTransition A (bufferedNativeTensorFrame A hA) p.1 i.1 a r y.2 = _
  rw [tensorNativeFrameTransition_eq_fderiv A hA p.1 i.1 a r hys]
  have hp := ((tensorLocalTransition_contDiffOn B hB p.2 i.2).contDiffAt
    ((tensorLocalChartOverlap_open B p.2 i.2).mem_nhds hyp)).differentiableAt (by simp)
  have hs := ((bufferedTransition_contDiffOn A hA p.1 i.1).contDiffAt
    ((bufferedChartOverlap_open A p.1 i.1).mem_nhds hys)).differentiableAt (by simp)
  have hprod := ((hp.hasFDerivAt.comp y hasFDerivAt_fst).prodMk
    (hs.hasFDerivAt.comp y hasFDerivAt_snd)).fderiv
  simp only [Function.comp_apply] at hprod
  change _ = parameterTensorJacobianEntryCLM a r
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
      (B.chart i.2 ((B.chart p.2).symm z.1),A.chart i.1 ((A.chart p.1).symm z.2))) y)
  rw [hprod]
  rfl

theorem tensorLocalNativeFrame_jet_le
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (p i : Fin A.count × Fin pcount) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ tensorLocalChartOverlap (parameterLocalProductFamily A B) p i) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (tensorLocalFrameTransition (parameterLocalProductFamily A B) (tensorLocalParameterFrame A B hA) p i a r) y‖ ≤
      ‖iteratedFDeriv ℝ (k+1) ((parameterLocalProductFamily A B).chart i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ := by
  let C := parameterLocalProductFamily A B
  have hder := (tensorLocalTransition_contDiffOn C
    (parameterLocalProductFamily_chart_mem A B hA hB) p i).fderiv_of_isOpen
    (tensorLocalChartOverlap_open C p i) (m := ∞) (by simp)
  have heq : tensorLocalFrameTransition C (tensorLocalParameterFrame A B hA) p i a r =ᶠ[𝓝 y]
      parameterTensorJacobianEntryCLM a r ∘ fderiv ℝ (C.chart i ∘ (C.chart p).symm) := by
    filter_upwards [(tensorLocalChartOverlap_open C p i).mem_nhds hy] with z hz
    exact tensorLocalNativeFrame_eq_fderiv A B hA hB p i a r hz
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  rw [(parameterTensorJacobianEntryCLM a r).iteratedFDeriv_comp_left
    (hder.contDiffAt ((tensorLocalChartOverlap_open C p i).mem_nhds hy)) (by simp)]
  apply ((parameterTensorJacobianEntryCLM a r).norm_compContinuousMultilinearMap_le _).trans
  rw [← norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (parameterTensorJacobianEntryCLM_norm_le a r)
    (norm_nonneg (iteratedFDeriv ℝ k (fderiv ℝ (C.chart i ∘ (C.chart p).symm)) y))

def tensorLocalOriginalInner
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (W : Set P) :=
  incrementsOriginalEvaluation A B.chart (bufferedInnerCoordinates A) (tensorLocalInner B) W

def tensorLocalOriginalSampling
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) :=
  incrementsOriginalEvaluation A B.chart (bufferedSamplingCoordinates A) (tensorLocalSamplingCoordinates B) univ

theorem tensorLocalOriginalInner_subset
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (W : Set P)
    (i : Fin A.count × Fin pcount) :
    tensorLocalOriginalInner A B W i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ h => h.1

theorem tensorLocalNativeModelCoordinates_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin pcount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B.chart i) :
    tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2) i y =
      incrementsOriginalTensorCoordinates A B.chart H i y :=
  tensorLocalParameterCoordinates_eq_original A B hA H i y hy

theorem tensorLocalNative_Cj_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (j : ℕ) (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, S i ⊆ tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) i) :
    paperAtlasCj j (tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) S =
    paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalDifferentiation A B.chart) S := by
  have hO : tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) =
      incrementsOriginalDifferentiation A B.chart := funext (parameterLocalProduct_targets A B)
  rw [hO]
  apply paperAtlasCj_congr_on
  · simpa only [hO] using hS
  · exact tensorLocalNativeModelCoordinates_eq_original A B hA H

theorem tensorLocalNative_weighted_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (base m : ℕ) (t : ℝ) (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, S i ⊆ tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) i) :
    paperAtlasWeighted base m t (tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) S =
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) S := by
  unfold paperAtlasWeighted
  exact Finset.sum_congr rfl (fun j _ => by rw [tensorLocalNative_Cj_eq_original A B hA H (j+base) S hS])

theorem tensorLocalNative_model_evaluation
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (W : Set P)
    (i : Fin A.count × Fin pcount) :
    tensorLocalModelEvaluation (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (Prod.fst ⁻¹' W) i = tensorLocalOriginalInner A B W i := by
  ext y
  simp only [tensorLocalModelEvaluation,modelCoordinateDomains,Set.mem_preimage,tensorLocalEvaluation,
    Set.mem_inter_iff,parameterLocalProductFamily_inner,Set.mem_prod,
    parameterTensorModelEquiv_symm_apply,tensorLocalOriginalInner,incrementsOriginalEvaluation,
    incrementsOriginalDifferentiation,Set.mem_setOf_eq,tensorLocalInner,bufferedInnerCoordinates]
  change (((_ ∧ _) ∧ (_ ∧ _)) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ _)
  tauto

theorem tensorLocalNative_sampling_subset
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (i : Fin A.count × Fin pcount) :
    tensorLocalModelSampling (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) i ⊆
      tensorLocalOriginalSampling A B i := by
  intro y hy
  have htarget : y ∈ incrementsOriginalDifferentiation A B.chart i := by
    rw [← parameterLocalProduct_targets A B i]
    exact tensorLocalModelSampling_subset_target _ _ _ hy
  change (parameterTensorModelEquiv n d).symm y ∈
    tensorLocalSamplingCoordinates (parameterLocalProductFamily A B) i at hy
  obtain ⟨z,hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner,hyball⟩ := mem_iUnion.mp hz
  rw [parameterLocalProductFamily_inner] at hzInner
  have hdist : dist ((parameterTensorModelEquiv n d).symm y) z < min B.buffer A.buffer := hyball
  rw [parameterTensorModelEquiv_symm_apply,Prod.dist_eq,max_lt_iff] at hdist
  exact ⟨htarget,mem_iUnion.mpr ⟨z.2,mem_iUnion.mpr ⟨hzInner.2,
    hdist.2.trans_le (min_le_right _ _)⟩⟩,
    mem_iUnion.mpr ⟨z.1,mem_iUnion.mpr ⟨hzInner.1,
    hdist.1.trans_le (min_le_left _ _)⟩⟩,Set.mem_univ _⟩

theorem tensorLocalNative_weighted_sampling_le_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t (tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (tensorLocalModelSampling (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) ≤
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) := by
  rw [tensorLocalNative_weighted_eq_original A B hA H base m t _ (tensorLocalModelSampling_subset_target _ _)]
  exact paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ (tensorLocalNative_sampling_subset A B)

#print axioms tensorLocalNativeFrame_jet_le
#print axioms tensorLocalNative_weighted_eq_original
#print axioms tensorLocalNative_sampling_subset

end
end GlobalEmbedding.Offline
