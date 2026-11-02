import Smoothing.TensorFrames
import GlobalEmbedding.Offline.BufferedSmoothing
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# One actual buffered smoothing of a bilinear tensor field

Source: tensor localization in (6.4). Each chart smooths the ordered
coefficients of the same tensor, reconstructs a genuine bilinear form in that
chart's frame at the output point, and glues these forms by the original square
partition. The frame changes are retained; the construction does not identify
matrices in different tangent frames. This file proves the exact algebra and
symmetry of that construction, including the signed-kernel case.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

set_option backward.isDefEq.respectTransparency false

section IntegralSymmetry

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- The actual Bochner integral preserves symmetry, also when its integrand
is not integrable (the total integral then is zero). No positive kernel is
assumed or asserted. -/
theorem integral_tensor_components_symmetric (mu : Measure X)
    (u : X → Fin (n * n) → ℝ)
    (hu : ∀ x i j, u x (finProdFinEquiv (i, j)) = u x (finProdFinEquiv (j, i)))
    (i j : Fin n) :
    (∫ x, u x ∂mu) (finProdFinEquiv (i, j)) =
      (∫ x, u x ∂mu) (finProdFinEquiv (j, i)) := by
  by_cases hI : Integrable u mu
  · rw [eval_integral (fun k => hI.eval k), eval_integral (fun k => hI.eval k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hu x i j)
  · simp only [integral_undef hI, Pi.zero_apply]

end IntegralSymmetry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [TopologicalSpace M] {n : ℕ}
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Components of the actual field in the i-th actual moving frame. -/
def tensorCoefficientField (A : BufferedAtlas M E)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : Fin A.count) (x : M) :
    Fin (n * n) → ℝ := tensorFrameComponents (b i x) (H x)

/-- An actual bilinear tensor field assembled after local convolution in
each frame. The global map smoother is not applied to unrelated matrices. -/
def bufferedTensorSmoothing (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (x : M) :
    LinearMap.BilinForm ℝ (V x) :=
  ∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
    (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x)

/-- The local convolution coefficients retain symmetry of the original
tensor. This includes the true coordinate indicator zero extension. -/
theorem bufferedLocalSmoothing_tensor_symmetric (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ x, (H x).IsSymm) (i : Fin A.count) (z : E) (a c : Fin n) :
    bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i z
        (finProdFinEquiv (a, c)) =
      bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i z
        (finProdFinEquiv (c, a)) := by
  apply integral_tensor_components_symmetric
  intro y r s
  by_cases hy : z - ell • y ∈ (A.chart i).target
  · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hy, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, tensorCoefficientField, tensorFrameComponents,
      Equiv.symm_apply_apply]
    rw [(hH ((A.chart i).symm (z - ell • y))).eq]
  · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hy, smul_zero, Pi.zero_apply]

/-- Symmetry survives actual frame reconstruction and the global sum. -/
theorem bufferedTensorSmoothing_isSymm (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ x, (H x).IsSymm) (x : M) :
    (bufferedTensorSmoothing A mu K ell chi b H x).IsSymm := by
  have hterm (i : Fin A.count) :
      (tensorFromFrameComponents (b i x)
        (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x)).IsSymm := by
    apply tensorFromFrameComponents_isSymm
    intro a c
    by_cases hx : x ∈ (A.chart i).source
    · simp only [bufferedChartSmoothing, Set.indicator_of_mem hx, Function.comp_apply]
      exact bufferedLocalSmoothing_tensor_symmetric A mu K ell b H hH i _ a c
    · simp only [bufferedChartSmoothing, Set.indicator_of_notMem hx, Pi.zero_apply]
  rw [LinearMap.BilinForm.isSymm_def]
  intro v w
  simp only [bufferedTensorSmoothing, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hterm i).eq]

/-- The genuine tensor smoothing error is the sum of reconstructed local
errors. All frame inverses are justified by the proved component bijection. -/
theorem bufferedTensorSmoothing_error_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (x : M) :
    bufferedTensorSmoothing A mu K ell chi b H x - H x =
      ∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i (A.chart i x) -
          bufferedCoordinateExtension A (tensorCoefficientField A b H i) i (A.chart i x)) := by
  have hsingle (i : Fin A.count) :
      chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x) -
        chi i x ^ 2 • H x =
      chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i (A.chart i x) -
          bufferedCoordinateExtension A (tensorCoefficientField A b H i) i (A.chart i x)) := by
    by_cases hi : chi i x = 0
    · simp only [hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]
      exact sub_self (0 : LinearMap.BilinForm ℝ (V x))
    · have hx := A.inner_subset i (hchiSupport i (subset_tsupport (chi i) hi))
      have hext : bufferedCoordinateExtension A (tensorCoefficientField A b H i) i
          (A.chart i x) = tensorFrameComponents (b i x) (H x) := by
        simp only [bufferedCoordinateExtension,
          Set.indicator_of_mem ((A.chart i).map_source hx), Function.comp_apply]
        exact congrArg (tensorCoefficientField A b H i) ((A.chart i).left_inv hx)
      rw [hext, tensorFromFrameComponents_sub, tensorFromFrameComponents_components]
      simp only [bufferedChartSmoothing, Set.indicator_of_mem hx, Function.comp_apply]
      exact (smul_sub (chi i x ^ 2)
        (tensorFromFrameComponents (b i x)
          (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i (A.chart i x)))
        (H x)).symm
  have hsum : (∑ i, chi i x ^ 2 • H x) = H x := by
    rw [← Finset.sum_smul, hpartition x, one_smul]
  unfold bufferedTensorSmoothing
  conv_lhs => rw [← hsum]
  calc
    _ = ∑ i, (chi i x ^ 2 • tensorFromFrameComponents (b i x)
          (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x) -
          chi i x ^ 2 • H x) := (Finset.sum_sub_distrib (s := Finset.univ)
          (fun i => chi i x ^ 2 • tensorFromFrameComponents (b i x)
            (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x))
          (fun i => chi i x ^ 2 • H x)).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => hsingle i)

/-- In any receiving frame the error has the required double transition
contraction. Thus derivatives of BOTH frame factors really occur downstream. -/
theorem bufferedTensorSmoothing_error_components (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (x : M)
    (c : Basis (Fin n) ℝ (V x)) (a d : Fin n) :
    tensorFrameComponents c (bufferedTensorSmoothing A mu K ell chi b H x - H x)
        (finProdFinEquiv (a, d)) =
      ∑ i, chi i x ^ 2 * ∑ r, ∑ s,
        (b i x).repr (c a) r *
          (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i (A.chart i x) -
            bufferedCoordinateExtension A (tensorCoefficientField A b H i) i (A.chart i x))
              (finProdFinEquiv (r, s)) * (b i x).repr (c d) s := by
  rw [bufferedTensorSmoothing_error_eq A mu K ell chi hchiSupport hpartition b H]
  simp only [tensorFrameComponents, Equiv.symm_apply_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorFromFrameComponents, Matrix.toBilin_apply]

end

end GlobalEmbedding.Offline
