import Smoothing.TensorFrames
import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The paper's actual source-chart tensor frame

The inverse chart differential gives a basis of the REAL tangent space.
Its basis vectors are exactly `incrementsOriginalSourceVector`. Consequently
the tensor algebra from `TensorFrames` applies to the original tensor ABI,
with arbitrary parameter dimension; no free matrix replaces the native tensor.
-/

open Manifold IsManifold Module GlobalEmbedding.Paper
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {n d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Smooth compatibility supplies both actual differentiable chart maps. -/
theorem bufferedChartMDifferentiable
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    (A.chart i).MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i)).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)).mdifferentiableOn (by simp)⟩

/-- The genuine chart basis, defined only at actual target points. -/
def bufferedSourceChartBasis
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (A.chart i).target) :
    Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((A.chart i).symm z)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
    (((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z).symm.trans
      ((bufferedChartMDifferentiable A hA i).symm.mfderiv hz)).toLinearEquiv)

/-- No abstract frame is inserted: this is the actual inverse derivative. -/
theorem bufferedSourceChartBasis_apply
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (A.chart i).target) (a : Fin n) :
    bufferedSourceChartBasis A hA i z hz a =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (A.chart i).symm z
        ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z).symm
          (EuclideanSpace.single a 1)) := by
  simp only [bufferedSourceChartBasis, Basis.map_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rfl

/-- A total family of actual tangent bases used by the global tensor
smoother. Outside the chart source the value is irrelevant after its cutoff;
inside it the frame is the actual inverse-chart derivative. -/
def bufferedNativeTensorFrame
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) (x : M) :
    Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := by
  classical
  exact if hx : x ∈ (A.chart i).source then
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      (((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (A.chart i x)).symm.trans
        ((bufferedChartMDifferentiable A hA i).mfderiv hx).symm).toLinearEquiv)
  else (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm.toLinearEquiv

/-- At every genuine target point, the total frame agrees with the actual
source chart basis, independent of any outside default. -/
theorem bufferedNativeTensorFrame_at_inverse
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (A.chart i).target) :
    bufferedNativeTensorFrame A hA i ((A.chart i).symm z) =
      bufferedSourceChartBasis A hA i z hz := by
  classical
  ext a
  unfold bufferedNativeTensorFrame
  simp only [dite_eq_left ((A.chart i).map_target hz), Basis.map_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    bufferedSourceChartBasis_apply]
  change mfderiv _ _ (A.chart i).symm (A.chart i ((A.chart i).symm z))
    ((tangentSpaceCastModel _ (A.chart i ((A.chart i).symm z))).symm
      (EuclideanSpace.single a 1)) = _
  exact congrArg (fun w : EuclideanSpace ℝ (Fin n) =>
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (A.chart i).symm w ((tangentSpaceCastModel _ w).symm
        (EuclideanSpace.single a 1)) : EuclideanSpace ℝ (Fin n)))
      ((A.chart i).right_inv hz)

/-- Equality with the original source vector works in nonzero parameter
dimension without differentiating parameters as tangent directions. -/
theorem bufferedSourceChartBasis_eq_originalSourceVector
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (y : Fin (n + d) → ℝ)
    (hy : incrementsOriginalSourcePoint y ∈ (A.chart i).target) (a : Fin n) :
    bufferedSourceChartBasis A hA i (incrementsOriginalSourcePoint y) hy a =
      incrementsOriginalSourceVector A i y a :=
  bufferedSourceChartBasis_apply A hA i _ hy a

/-- The original tensor-coordinate vector IS the component vector of the
same bilinear tensor in the actual chart basis. -/
theorem incrementsOriginalTensorCoordinates_eq_frameComponents
    {P : Type*} [TopologicalSpace P] {c : ℕ}
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    incrementsOriginalTensorCoordinates A B H i y =
      tensorFrameComponents
        (bufferedSourceChartBasis A hA i.1 (incrementsOriginalSourcePoint y) hy.1)
        (H (incrementsOriginalJointPoint A B i y).1
          (incrementsOriginalJointPoint A B i y).2) := by
  funext k
  simp only [incrementsOriginalTensorCoordinates, tensorFrameComponents,
    bufferedSourceChartBasis_eq_originalSourceVector]
  rfl

/-- Reconstruction of ALL original ordered coefficients returns the SAME
native tensor, including arbitrary finite-dimensional parameters. -/
theorem reconstruct_incrementsOriginalTensorCoordinates
    {P : Type*} [TopologicalSpace P] {c : ℕ}
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    tensorFromFrameComponents
      (bufferedSourceChartBasis A hA i.1 (incrementsOriginalSourcePoint y) hy.1)
      (incrementsOriginalTensorCoordinates A B H i y) =
        H (incrementsOriginalJointPoint A B i y).1
          (incrementsOriginalJointPoint A B i y).2 := by
  rw [incrementsOriginalTensorCoordinates_eq_frameComponents A hA B H i y hy]
  exact tensorFromFrameComponents_components _ _

/-- Exact original ABI for the total native frame used by the tensor
smoothing construction, with arbitrary source and parameter dimensions. -/
theorem incrementsOriginalTensorCoordinates_eq_nativeFrame
    {P : Type*} [TopologicalSpace P] {c : ℕ}
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    incrementsOriginalTensorCoordinates A B H i y =
      tensorFrameComponents
        (bufferedNativeTensorFrame A hA i.1 (incrementsOriginalJointPoint A B i y).2)
        (H (incrementsOriginalJointPoint A B i y).1
          (incrementsOriginalJointPoint A B i y).2) := by
  change _ = tensorFrameComponents
    (bufferedNativeTensorFrame A hA i.1
      ((A.chart i.1).symm (incrementsOriginalSourcePoint y))) _
  rw [bufferedNativeTensorFrame_at_inverse A hA i.1 _ hy.1]
  exact incrementsOriginalTensorCoordinates_eq_frameComponents A hA B H i y hy

end

end GlobalEmbedding.Offline
