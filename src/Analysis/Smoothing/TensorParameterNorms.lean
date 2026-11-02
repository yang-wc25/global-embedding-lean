import Smoothing.TensorParameterCoordinates

/-!
# Exact original tensor norms on genuine parameter/source product domains

This bridge uses the frozen original partial-derivative chart maximum.
Differentiation remains on the original open product target. Evaluation uses
the actual buffered inner sets and fixed sampling buffers. The joint sampling
buffer is contained in the product of the original two sampling buffers, so
source budgets on those original domains control the actual convolution.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

section NormMonotonicity

variable {ι : Type*} [Fintype ι] {s q : ℕ}

theorem paperAtlasCj_mono_evaluation (j : ℕ) (f : ι → (Fin s → ℝ) → Fin q → ℝ)
    (O S R : ι → Set (Fin s → ℝ)) (hSR : ∀ i, S i ⊆ R i) :
    paperAtlasCj j f O S ≤ paperAtlasCj j f O R := by
  unfold paperAtlasCj paperCoordinateCj
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply iSup_le
  intro l
  apply le_iSup_of_le l
  apply iSup_le
  intro x
  exact le_iSup_of_le (⟨x.val, hSR i x.property⟩ : R i) le_rfl

theorem paperAtlasWeighted_mono_evaluation (base m : ℕ) (t : ℝ)
    (f : ι → (Fin s → ℝ) → Fin q → ℝ)
    (O S R : ι → Set (Fin s → ℝ)) (hSR : ∀ i, S i ⊆ R i) :
    paperAtlasWeighted base m t f O S ≤ paperAtlasWeighted base m t f O R := by
  unfold paperAtlasWeighted
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul le_rfl (paperAtlasCj_mono_evaluation (j + base) f O S R hSR) (by positivity) (by positivity)

end NormMonotonicity

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Original product inner evaluation, with parameter evaluation on the
whole fixed parameter manifold and separate open differentiation charts. -/
def parameterTensorOriginalInner
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) :=
  incrementsOriginalEvaluation A B.chart (bufferedInnerCoordinates A) (bufferedInnerCoordinates B) univ

/-- Original independent fixed source/parameter sampling buffers. -/
def parameterTensorOriginalSampling
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) :=
  incrementsOriginalEvaluation A B.chart (bufferedSamplingCoordinates A) (bufferedSamplingCoordinates B) univ

theorem parameterTensorOriginalInner_subset
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    parameterTensorOriginalInner A B i ⊆ incrementsOriginalDifferentiation A B.chart i :=
  fun _ hy => hy.1

theorem parameterTensorOriginalSampling_subset
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    parameterTensorOriginalSampling A B i ⊆ incrementsOriginalDifferentiation A B.chart i :=
  fun _ hy => hy.1

/-- The receiving inner domain is precisely the original product evaluation set. -/
theorem parameterTensorModel_inner
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    bufferedModelInner (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
      (parameterTensorAtlasIndex A B i) = parameterTensorOriginalInner A B i := by
  ext y
  simp only [bufferedModelInner, modelCoordinateDomains, Set.mem_preimage,
    parameterTensorModelEquiv_symm_apply, parameterTensorAtlasIndex, Equiv.trans_apply,
    Equiv.prodComm_apply, parameterProductAtlas, parameterProductIndex, Equiv.symm_apply_apply,
    bufferedInnerCoordinates, parameterTensorOriginalInner, incrementsOriginalEvaluation,
    incrementsOriginalDifferentiation, Set.mem_setOf_eq, Set.mem_univ, and_true]
  change ((_ ∧ _) ∧ (_ ∧ _)) ↔ ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _))
  tauto

/-- A joint fixed buffer is contained in the two original fixed buffers. -/
theorem parameterTensorModel_sampling_subset
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (i : Fin A.count × Fin B.count) :
    bufferedModelSampling (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
      (parameterTensorAtlasIndex A B i) ⊆ parameterTensorOriginalSampling A B i := by
  intro y hy
  have htarget := bufferedModelSampling_subset_target (parameterProductAtlas A B)
    (parameterTensorModelEquiv n d) (parameterTensorAtlasIndex A B i) hy
  rw [parameterTensorModel_targets] at htarget
  change (parameterTensorModelEquiv n d).symm y ∈
    bufferedSamplingCoordinates (parameterProductAtlas A B) (parameterTensorAtlasIndex A B i) at hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hz' : z.1 ∈ bufferedInnerCoordinates B i.2 ∧ z.2 ∈ bufferedInnerCoordinates A i.1 := by
    simpa only [bufferedInnerCoordinates, parameterProductAtlas, parameterTensorAtlasIndex,
      Equiv.trans_apply, Equiv.prodComm_apply, parameterProductIndex, Equiv.symm_apply_apply,
      OpenPartialHomeomorph.prod_symm_apply, Prod.swap,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage] using And.intro (And.intro hzInner.1.1 hzInner.2.1)
        (And.intro hzInner.1.2 hzInner.2.2)
  have hdist : dist ((parameterTensorModelEquiv n d).symm y) z < min B.buffer A.buffer := hyball
  rw [parameterTensorModelEquiv_symm_apply, Prod.dist_eq, max_lt_iff] at hdist
  refine ⟨htarget, ?_, ?_, Set.mem_univ _⟩
  · exact mem_iUnion.mpr ⟨z.2, mem_iUnion.mpr ⟨hz'.2,
      hdist.2.trans_le (min_le_right _ _)⟩⟩
  · exact mem_iUnion.mpr ⟨z.1, mem_iUnion.mpr ⟨hz'.1,
      hdist.1.trans_le (min_le_left _ _)⟩⟩

/-- Original coordinate smoothness supplies exactly the local native tensor
smoothness used by the actual product convolution. -/
theorem parameterTensorNativeCoordinates_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (j : Fin (parameterProductAtlas A B).count) :
    ContDiffOn ℝ ∞
      (tensorCoefficientField (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA)
        (fun z => H z.1 z.2) j ∘ ((parameterProductAtlas A B).chart j).symm)
      ((parameterProductAtlas A B).chart j).target := by
  obtain ⟨i, rfl⟩ := (parameterTensorAtlasIndex A B).surjective j
  let c := parameterTensorModelEquiv n d
  have hmap : MapsTo c ((parameterProductAtlas A B).chart (parameterTensorAtlasIndex A B i)).target
      (incrementsOriginalDifferentiation A B.chart i) := by
    intro z hz
    rw [← parameterTensorModel_targets A B i]
    change (parameterTensorModelEquiv n d).symm (c z) ∈
      ((parameterProductAtlas A B).chart (parameterTensorAtlasIndex A B i)).target
    simpa only [c, ContinuousLinearEquiv.symm_apply_apply] using hz
  apply ((hH i).comp c.contDiff.contDiffOn hmap).congr
  intro z hz
  have h := parameterTensorModelCoordinates_eq_original A B hA H i (c z) (hmap hz)
  simpa only [bufferedTensorModelCoordinates, modelCoordinateFamily, Function.comp_apply,
    c, ContinuousLinearEquiv.symm_apply_apply, bufferedTensorNativeCoordinates] using h

/-- The original chart maximum is exactly retained after the genuine index
and coordinate equivalences, on every true evaluation subdomain. -/
theorem parameterTensor_paperAtlasCj_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (j : ℕ) (S : Fin (parameterProductAtlas A B).count → Set (Fin (n + d) → ℝ))
    (hS : ∀ i, S i ⊆ bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d) i) :
    paperAtlasCj j
      (bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
        (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2))
      (bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d)) S =
    paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  rw [← paperAtlasCj_reindex (parameterTensorAtlasIndex A B)]
  have hO : (fun i => bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
      (parameterTensorAtlasIndex A B i)) = incrementsOriginalDifferentiation A B.chart :=
    funext (parameterTensorModel_targets A B)
  rw [hO]
  apply paperAtlasCj_congr_on
  · intro i y hy
    rw [← parameterTensorModel_targets A B i]
    exact hS _ hy
  · intro i y hy
    exact parameterTensorModelCoordinates_eq_original A B hA H i y hy

theorem parameterTensor_paperAtlasWeighted_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (base m : ℕ) (t : ℝ)
    (S : Fin (parameterProductAtlas A B).count → Set (Fin (n + d) → ℝ))
    (hS : ∀ i, S i ⊆ bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d) i) :
    paperAtlasWeighted base m t
      (bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
        (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2))
      (bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d)) S =
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j _
  rw [parameterTensor_paperAtlasCj_eq_original A B hA H (j + base) S hS]

/-- Native product-coordinate smoothness gives the frozen original tensor
coordinate smoothness for the same bilinear field. -/
theorem parameterTensorOriginalCoordinates_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ j, ContDiffOn ℝ ∞
      (tensorCoefficientField (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA)
        (fun z => H z.1 z.2) j ∘ ((parameterProductAtlas A B).chart j).symm)
      ((parameterProductAtlas A B).chart j).target)
    (i : Fin A.count × Fin B.count) :
    ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i) := by
  have h := bufferedTensorModelCoordinates_contDiffOn (parameterProductAtlas A B)
    (parameterTensorModelEquiv n d) (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2) hH
    (parameterTensorAtlasIndex A B i)
  rw [parameterTensorModel_targets] at h
  apply h.congr
  intro y hy
  exact (parameterTensorModelCoordinates_eq_original A B hA H i y hy).symm

/-- Exact output weighted norm on the original inner domains. -/
theorem parameterTensor_weighted_inner_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
        (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2))
      (bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d))
      (bufferedModelInner (parameterProductAtlas A B) (parameterTensorModelEquiv n d)) =
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalInner A B) := by
  rw [parameterTensor_paperAtlasWeighted_eq_original A B hA H base m t _
    (bufferedModelInner_subset_target _ _)]
  congr 1
  exact funext (parameterTensorModel_inner A B)

/-- The actual convolution's source Cj norm is controlled by the original
source/parameter buffer Cj norm, with no coordinate or chart-count loss. -/
theorem parameterTensor_Cj_sampling_le_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) (j : ℕ) :
    paperAtlasCj j
      (bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
        (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2))
      (bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d))
      (bufferedModelSampling (parameterProductAtlas A B) (parameterTensorModelEquiv n d)) ≤
    paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  rw [parameterTensor_paperAtlasCj_eq_original A B hA H j _
    (bufferedModelSampling_subset_target _ _)]
  exact paperAtlasCj_mono_evaluation _ _ _ _ _ (parameterTensorModel_sampling_subset A B)

theorem parameterTensor_weighted_sampling_le_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (bufferedTensorModelCoordinates (parameterProductAtlas A B) (parameterTensorModelEquiv n d)
        (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2))
      (bufferedModelTargets (parameterProductAtlas A B) (parameterTensorModelEquiv n d))
      (bufferedModelSampling (parameterProductAtlas A B) (parameterTensorModelEquiv n d)) ≤
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  rw [parameterTensor_paperAtlasWeighted_eq_original A B hA H base m t _
    (bufferedModelSampling_subset_target _ _)]
  exact paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ (parameterTensorModel_sampling_subset A B)

end

end GlobalEmbedding.Offline
