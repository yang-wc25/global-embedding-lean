import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The original linear tensor functional is evaluated by its own symmetric
coordinate coefficients and the original tensor coordinates. No estimate of
an arbitrary skew extension of that functional is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

private theorem symmetric_matrix_expansion {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) :
    C = ∑ r, ∑ s, C r s • ((1/2 : ℝ) •
      (Matrix.single r s 1 + (Matrix.single r s 1).transpose)) := by
  ext i j
  have hc := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply] at hc
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.single_apply, ite_and, mul_add,
    Finset.sum_add_distrib, hc]
  ring

private theorem symmetric_bilinear_coordinate_expansion
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : V ≃ₗ[ℝ] (Fin n → ℝ)) (T : LinearMap.BilinForm ℝ V)
    (hT : T.IsSymm) :
    T = ∑ r, ∑ s,
      T (a.symm (Pi.single r 1)) (a.symm (Pi.single s 1)) •
      LinearMap.BilinForm.comp
        ((1/2 : ℝ) • (Matrix.single r s (1 : ℝ) + (Matrix.single r s (1 : ℝ)).transpose)).toBilin'
        a.toLinearMap a.toLinearMap := by
  let C := LinearMap.BilinForm.toMatrix'
    (T.comp a.symm.toLinearMap a.symm.toLinearMap)
  have hC : C.IsSymm := by
    ext r s
    exact hT.eq _ _
  have he := symmetric_matrix_expansion C hC
  ext v w
  have hvw := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B.toBilin' (a v) (a w)) he
  simpa only [C, Matrix.toBilin'_toMatrix', LinearMap.BilinForm.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.toMatrix'_apply] using hvw

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace P]

/-- Exact evaluation on the SAME native symmetric tensor. Its coefficients are
the frozen original inverse-chart tensor values and the frozen original
forward-chart symmetric functional values, including all ordered pairs. -/
theorem actual_original_linear_argument_tensor_pairing
    (D : IncrementsOriginalNativeData n d N M P)
    (hAtlas : IsSmoothBufferedAtlas D.atlas)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n+d) → ℝ)
    (hy : incrementsOriginalSourcePoint y ∈ (D.atlas.chart i.1).target)
    (hinput : (input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2).IsSymm) :
    D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
      (input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2) =
    ∑ k, incrementsOriginalLinearArgumentCoordinates D ν i y k *
      incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i y k := by
  classical
  let chart := D.atlas.chart i.1
  have hchart : chart.MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) := by
    have h1 : chart ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 M :=
      IsManifold.maximalAtlas_subset_of_le (by simp) (hAtlas.chart_mem i.1)
    constructor
    · intro x hx
      exact (mdifferentiableAt_of_mem_maximalAtlas h1 hx).mdifferentiableWithinAt
    · intro x hx
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas h1 hx).mdifferentiableWithinAt
  let a : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (chart.symm (incrementsOriginalSourcePoint y)) ≃L[ℝ] (Fin n → ℝ) :=
    (hchart.symm.mfderiv hy).symm.trans (EuclideanSpace.equiv (Fin n) ℝ)
  let T := input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
  have ha : a.toLinearEquiv.toLinearMap =
      (incrementsOriginalSourceChartDifferential D i.1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2).toLinearMap := by
    rfl
  have hb (r : Fin n) : a.toLinearEquiv.symm (Pi.single r 1) =
      incrementsOriginalSourceVector D.atlas i.1 y r := by
    rfl
  have he := symmetric_bilinear_coordinate_expansion a.toLinearEquiv T hinput
  simp only [ha, hb] at he
  change T = ∑ r, ∑ s,
    T (incrementsOriginalSourceVector D.atlas i.1 y r)
      (incrementsOriginalSourceVector D.atlas i.1 y s) •
        (incrementsOriginalSymmetricCoordinateTensor D i.1
          (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2 r s).val at he
  have heL := congrArg (D.linearArgument ν
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2) he
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simpa only [incrementsOriginalLinearArgumentCoordinates,
    incrementsOriginalTensorCoordinates, Equiv.symm_apply_apply, map_sum,
    map_smul, smul_eq_mul, T, mul_comm] using heL

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_linear_argument_tensor_pairing
