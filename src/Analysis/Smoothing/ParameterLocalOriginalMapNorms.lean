import Smoothing.ParameterLocalMapWeighted
import Smoothing.TensorLocalNative

/-!
# Original map ABI and the same Euclidean local smoother

The actual signed integral commutes with the target linear equivalence. The
norms are literal original total-joint norms with the source-first ABI. Input
sampling is the genuine independent source/parameter buffer; the parameter
set in that source domain is univ, and is never silently replaced by K.
-/
open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

section Naturality

variable {ι E F G M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace E] [TopologicalSpace M]

omit [NormedSpace ℝ E] [MeasurableSpace E] in
/-- Actual coordinate zero extension commutes with a genuine linear equivalence. -/
theorem tensorLocalCoordinateExtension_equiv (A : TensorBufferedChartFamily ι M E) (e : F ≃L[ℝ] G)
    (u : M → F) (i : ι) :
    tensorLocalCoordinateExtension A (e ∘ u) i = e ∘ tensorLocalCoordinateExtension A u i := by
  funext z
  by_cases hz : z ∈ (A.chart i).target
  · simp only [tensorLocalCoordinateExtension, Set.indicator_of_mem hz, Function.comp_apply]
  · simp only [tensorLocalCoordinateExtension, Set.indicator_of_notMem hz, Function.comp_apply, map_zero]

/-- Naturality of the actual local integral, including the Bochner convention
outside the buffered region. Invertibility preserves integrability. -/
theorem tensorLocalConvolution_equiv (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (e : F ≃L[ℝ] G) (u : M → F) (i : ι) :
    tensorLocalConvolution A mu K ell (e ∘ u) i = e ∘ tensorLocalConvolution A mu K ell u i := by
  funext z
  change (∫ y, K y • tensorLocalCoordinateExtension A (e ∘ u) i (z - ell • y) ∂mu) =
    e (∫ y, K y • tensorLocalCoordinateExtension A u i (z - ell • y) ∂mu)
  rw [tensorLocalCoordinateExtension_equiv]
  simpa only [Function.comp_apply, map_smul] using e.integral_comp_comm
    (fun y => K y • tensorLocalCoordinateExtension A u i (z - ell • y))

/-- The actual global operator commutes with the same linear target equivalence.
This is an equality of the original finite sums and actual convolution integrals. -/
theorem parameterLocalMapSmoothing_equiv (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ) (e : F ≃L[ℝ] G) (u : M → F) :
    parameterLocalMapSmoothing A mu K ell chi (e ∘ u) = e ∘ parameterLocalMapSmoothing A mu K ell chi u := by
  funext x
  change (∑ i, chi i x ^ 2 • tensorLocalChartConvolution A mu K ell (e ∘ u) i x) =
    e (∑ i, chi i x ^ 2 • tensorLocalChartConvolution A mu K ell u i x)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ (A.chart i).source
  · simp only [tensorLocalChartConvolution, Set.indicator_of_mem hx,
      Function.comp_apply, tensorLocalConvolution_equiv, map_smul]
  · simp only [tensorLocalChartConvolution, Set.indicator_of_notMem hx,
      smul_zero, map_zero]

end Naturality

variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterLocalOriginalMapNormsChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterLocalOriginalMapNormsIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ

theorem parameterLocalMapCoordinates_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) :
    parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u) =
      incrementsOriginalMapCoordinates A B.chart u := rfl

theorem parameterLocalMap_weighted_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) (base m : ℕ) (t : ℝ) (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ)) :
    paperAtlasWeighted base m t
      (parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) S =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) S := by
  rw [parameterLocalMapCoordinates_eq_original]
  congr 1
  exact funext (parameterLocalProduct_targets A B)

theorem parameterLocalMap_weighted_inner_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) (W : Set P) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (tensorLocalModelEvaluation (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (Prod.fst ⁻¹' W)) =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W) := by
  rw [parameterLocalMap_weighted_eq_original]
  congr 1
  exact funext (tensorLocalNative_model_evaluation A B W)

theorem parameterLocalMap_weighted_sampling_le_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (tensorLocalModelSampling (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) ≤
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) := by
  rw [parameterLocalMap_weighted_eq_original]
  exact paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ (tensorLocalNative_sampling_subset A B)

/-- Original map-coordinate smoothness supplies actual native Pi coefficients. -/
theorem parameterLocalMapInputPi_contDiffOn
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey)
    (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i)) (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ ((cy ∘ u) ∘ ((parameterLocalProductFamily A B).chart i).symm)
      ((parameterLocalProductFamily A B).chart i).target := by
  let c := parameterTensorModelEquiv n d
  have hmap : MapsTo c ((parameterLocalProductFamily A B).chart i).target
      (incrementsOriginalDifferentiation A B.chart i) := by
    intro z hz
    rw [← parameterLocalProduct_targets A B i]
    change c.symm (c z) ∈ ((parameterLocalProductFamily A B).chart i).target
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
  apply ((hu i).comp c.contDiff.contDiffOn hmap).congr
  intro z _
  change _ = (cy ∘ u) (((parameterLocalProductFamily A B).chart i).symm (c.symm (c z)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem parameterLocalMapInput_contDiffOn
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey)
    (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i)) (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (u ∘ ((parameterLocalProductFamily A B).chart i).symm)
      ((parameterLocalProductFamily A B).chart i).target := by
  have h := (cy).symm.contDiff.comp_contDiffOn (parameterLocalMapInputPi_contDiffOn A B u hu i)
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using h

#print axioms parameterLocalMapSmoothing_equiv
#print axioms parameterLocalMapInput_contDiffOn
#print axioms parameterLocalMap_weighted_sampling_le_original
end
end GlobalEmbedding.Continuation
