import Smoothing.TensorLocalOriginalGain
import Smoothing.TensorEllipticity

/-!
# Actual native parameterized tensor positivity from the smoothing reserve

The signed smoother is proved to remain in the positive cone when its actual
original C0 tail fits the separately retained ellipticity margin. The output
positive definiteness is a conclusion, never a premise. Both original chart
frames and their explicit n² coefficient-to-quadratic cost remain visible.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

section Symmetry
variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [TopologicalSpace M] {n : ℕ}
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- The local convolution coefficients retain symmetry of the original
tensor. This includes the true coordinate indicator zero extension. -/
theorem tensorFamilyConvolution_symmetric (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ x, (H x).IsSymm) (i : ι) (z : E) (a c : Fin n) :
    tensorLocalConvolution A mu K ell (tensorLocalFieldCoefficients b H i) i z
        (finProdFinEquiv (a, c)) =
      tensorLocalConvolution A mu K ell (tensorLocalFieldCoefficients b H i) i z
        (finProdFinEquiv (c, a)) := by
  apply integral_tensor_components_symmetric
  intro y r s
  by_cases hy : z - ell • y ∈ (A.chart i).target
  · simp only [tensorLocalCoordinateExtension, Set.indicator_of_mem hy, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, tensorLocalFieldCoefficients, tensorFrameComponents,
      Equiv.symm_apply_apply]
    rw [(hH ((A.chart i).symm (z - ell • y))).eq]
  · simp only [tensorLocalCoordinateExtension, Set.indicator_of_notMem hy, smul_zero, Pi.zero_apply]

/-- Symmetry survives actual frame reconstruction and the global sum. -/
theorem tensorFamilySmoothing_isSymm (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ x, (H x).IsSymm) (x : M) :
    (tensorLocalFieldSmoothing A mu K ell chi b H x).IsSymm := by
  have hterm (i : ι) :
      (tensorFromFrameComponents (b i x)
        (tensorLocalChartConvolution A mu K ell (tensorLocalFieldCoefficients b H i) i x)).IsSymm := by
    apply tensorFromFrameComponents_isSymm
    intro a c
    by_cases hx : x ∈ (A.chart i).source
    · simp only [tensorLocalChartConvolution, Set.indicator_of_mem hx, Function.comp_apply]
      exact tensorFamilyConvolution_symmetric A mu K ell b H hH i _ a c
    · simp only [tensorLocalChartConvolution, Set.indicator_of_notMem hx, Pi.zero_apply]
  rw [LinearMap.BilinForm.isSymm_def]
  intro v w
  simp only [tensorLocalFieldSmoothing, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hterm i).eq]

end Symmetry

variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The true original source frame at a true original joint coordinate point. -/
def tensorLocalOriginalFrame
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (i : Fin A.count × Fin pcount) (y : Fin (n + d) → ℝ) :
    Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (incrementsOriginalJointPoint A B.chart i y).2) :=
  bufferedNativeTensorFrame A hA i.1 (incrementsOriginalJointPoint A B.chart i y).2

/-- A finite actual original coefficient C0 error and its numerical reserve
retain half the original ellipticity in every true original chart. -/
theorem tensorLocal_half_ellipticity_of_original_C0
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (H S : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (W : Set P) (alpha eps : ℝ) (heps : 0 ≤ eps)
    (hfinite : paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x))
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W) ≠ ⊤)
    (herror : (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x))
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W)).toReal ≤ eps)
    (hH : ∀ i y, y ∈ tensorLocalOriginalInner A B W i →
      ∀ v, alpha * ‖tensorFrameVector (tensorLocalOriginalFrame A B hA i y) v‖ ^ 2 ≤
        H (incrementsOriginalJointPoint A B.chart i y).1 (incrementsOriginalJointPoint A B.chart i y).2 v v)
    (hreserve : (n : ℝ) ^ 2 * eps ≤ alpha / 2) :
    ∀ i y, y ∈ tensorLocalOriginalInner A B W i →
      ∀ v, (alpha / 2) * ‖tensorFrameVector (tensorLocalOriginalFrame A B hA i y) v‖ ^ 2 ≤
        S (incrementsOriginalJointPoint A B.chart i y).1 (incrementsOriginalJointPoint A B.chart i y).2 v v := by
  intro i y hy v
  have hval := paperAtlasC0_value_le
    (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x))
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W) hfinite i hy
  rw [incrementsOriginalTensorCoordinates_eq_nativeFrame A hA B.chart
    (fun p x => H p x - S p x) i y hy.1] at hval
  exact tensor_half_ellipticity (tensorLocalOriginalFrame A B hA i y) _ _ alpha eps heps
    (hH i y hy) (hval.trans herror) hreserve v

/-- The actual product inner charts cover the stated region W. Their
half-ellipticity gives strict positive definiteness at each point over W.
The final signed-smoothing theorem derives this cover from its own cutoffs. -/
theorem tensorLocal_positive_of_inner_half_ellipticity
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (S : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (W : Set P) (alpha : ℝ) (halpha : 0 < alpha)
    (hcover : ∀ p ∈ W, ∀ x, ∃ i, (p,x) ∈ (parameterLocalProductFamily A B).inner i)
    (hS : ∀ i y, y ∈ tensorLocalOriginalInner A B W i →
      ∀ v, (alpha / 2) * ‖tensorFrameVector (tensorLocalOriginalFrame A B hA i y) v‖ ^ 2 ≤
        S (incrementsOriginalJointPoint A B.chart i y).1 (incrementsOriginalJointPoint A B.chart i y).2 v v) :
    ∀ p ∈ W, ∀ x, ∀ v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x, v ≠ 0 → 0 < S p x v v := by
  intro p hpW x
  obtain ⟨⟨i,j⟩,hj,hi⟩ := hcover p hpW x
  let y := parameterTensorModelEquiv n d (B.chart j p, A.chart i x)
  have hcoords : (incrementsOriginalParameterPoint y, incrementsOriginalSourcePoint y) =
      (B.chart j p, A.chart i x) := by
    rw [← parameterTensorModelEquiv_symm_apply]
    exact (parameterTensorModelEquiv n d).symm_apply_apply _
  have hp : incrementsOriginalParameterPoint y = B.chart j p := congrArg Prod.fst hcoords
  have hx : incrementsOriginalSourcePoint y = A.chart i x := congrArg Prod.snd hcoords
  have hpoint : incrementsOriginalJointPoint A B.chart (i, j) y = (p, x) := by
    simp only [incrementsOriginalJointPoint, hp, hx,
      (A.chart i).left_inv (A.inner_subset i hi), (B.chart j).left_inv (B.inner_subset j hj)]
  have hy : y ∈ tensorLocalOriginalInner A B W (i, j) := by
    change (incrementsOriginalSourcePoint y ∈ (A.chart i).target ∧
      incrementsOriginalParameterPoint y ∈ (B.chart j).target) ∧
      incrementsOriginalSourcePoint y ∈ bufferedInnerCoordinates A i ∧
      incrementsOriginalParameterPoint y ∈ tensorLocalInner B j ∧ _
    rw [hp, hx]
    exact ⟨⟨(A.chart i).map_source (A.inner_subset i hi), (B.chart j).map_source (B.inner_subset j hj)⟩,
      bufferedInnerCoordinates_mem A i hi, tensorLocalInner_mem B j hj, by
        simpa only [hpoint] using hpW⟩
  apply tensor_positive_of_half_ellipticity (bufferedNativeTensorFrame A hA i x) (S p x) alpha halpha
  intro v
  have h := hS (i, j) y hy v
  have heq := congrArg (fun z : P × M =>
    alpha / 2 * ‖tensorFrameVector (bufferedNativeTensorFrame A hA i z.2)
      (v : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
        S z.1 z.2 (v : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))) hpoint
  exact heq.mp h

local instance tensorLocalPositiveChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance tensorLocalPositiveManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- The actual signed tensor smoothing is jointly smooth, symmetric and
strictly positive once the PROVED original C0 tail fits the original fixed
ellipticity reserve. No bound on an output tensor and no positivity of the
kernel is assumed; the only numerical restriction is the displayed tail size. -/
theorem fixedKernel_original_local_parameter_tensor_smoothing_positive
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (W : Set P) (hW : IsOpen W) (hpartition : ∀ z : P × M, z.1 ∈ W → ∑ i, chi i z ^ 2 = 1)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (hsymm : ∀ p x, (H p x).IsSymm)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (hC0 : paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal ≤ budget)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hEll : ∀ i y, y ∈ tensorLocalOriginalInner A B W i →
      ∀ v, alpha * ‖tensorFrameVector (tensorLocalOriginalFrame A B hA i y) v‖ ^ 2 ≤
        H (incrementsOriginalJointPoint A B.chart i y).1 (incrementsOriginalJointPoint A B.chart i y).2 v v)
    (hreserve :
      let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
      (n : ℝ) ^ 2 *
        (modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d) mu
          (normalizedSmoothingBase mu rho hrho) Bc T (fun j => T (j + 1)) D 0 0 r *
          (budget * (ell / t) ^ r +
            (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
              (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal *
                (tau / t) ^ r)) ≤ alpha / 2) :
    let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    let K := fixedSmoothingKernel mu rho hrho r
    let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart S i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    (∀ p x, (S p x).IsSymm) ∧
    (∀ i y, y ∈ tensorLocalOriginalInner A B W i →
      ∀ v, (alpha / 2) * ‖tensorFrameVector (tensorLocalOriginalFrame A B hA i y) v‖ ^ 2 ≤
        S (incrementsOriginalJointPoint A B.chart i y).1 (incrementsOriginalJointPoint A B.chart i y).2 v v) ∧
    (∀ p ∈ W, ∀ x, ∀ v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x, v ≠ 0 → 0 < S p x v v) := by
  dsimp only
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let K := fixedSmoothingKernel mu rho hrho r
  let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
  let eps := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d) mu
    (normalizedSmoothingBase mu rho hrho) Bc T (fun j => T (j + 1)) D 0 0 r *
    (budget * (ell / t) ^ r +
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal * (tau / t) ^ r)
  have hNm : paperAtlasWeighted 0 0 t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤ := by
    simpa only [paperAtlasWeighted, Finset.sum_range_one, pow_zero, one_mul, zero_add] using hC0
  have h := fixedKernel_original_local_parameter_tensor_smoothing_tail A B hA hB rho hrho hbuffer 0 r
    htau htaul helt ht1 chi hchi hchiSupport W hW hpartition H hH Bc T hBc hT D hD hweight htransition
    hNr hNm budget hbudget
  dsimp only at h
  simp only [paperAtlasWeighted, Finset.sum_range_one, pow_zero, one_mul, zero_add] at h
  have he : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x))
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W)).toReal ≤ eps := h.2.2
  have heps : 0 ≤ eps := ENNReal.toReal_nonneg.trans he
  have hHalf := tensorLocal_half_ellipticity_of_original_C0 A B hA H S W alpha eps heps
    h.2.1 he hEll hreserve
  have hcover : ∀ p ∈ W, ∀ x, ∃ i, (p,x) ∈ (parameterLocalProductFamily A B).inner i := by
    intro p hp x
    have hsum : (∑ i, chi i (p,x)^2) ≠ 0 := by rw [hpartition (p,x) hp]; exact one_ne_zero
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    refine ⟨i,hchiSupport i (subset_tsupport (chi i) ?_)⟩
    intro hz
    exact hi (by simp only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  refine ⟨h.1,?_,hHalf,tensorLocal_positive_of_inner_half_ellipticity A B hA S W alpha halpha hcover hHalf⟩
  intro p x
  exact tensorFamilySmoothing_isSymm (parameterLocalProductFamily A B) mu K ell chi
    (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2) (fun z => hsymm z.1 z.2) (p,x)

#print axioms fixedKernel_original_local_parameter_tensor_smoothing_positive

end
end GlobalEmbedding.Offline
