import FaithfulRepair.OriginalTensorFrames
import Repair.EndpointLinearCoordinateFormula

/-!
# The original linear tensor functional under both genuine coframe factors

The input is the same native ell_nu.  Only its values on the same symmetric
coordinate tensors are used.  A tensor's slots transform by the forward
overlap Jacobian, while these dual coefficients transform by the reverse
coframe; confusing those two directions would invalidate the original input
profile.  The identities below make that distinction explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Module
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulIntegration

private theorem symmetric_sum_identity {n : ℕ}
    (R : Fin n → Fin n → ℝ) (u v : Fin n → ℝ) (r s : Fin n) :
    (1/2 : ℝ) * ((∑ a, R a r * u a) * (∑ b, R b s * v b) +
      (∑ a, R a s * u a) * (∑ b, R b r * v b)) =
      ∑ a, ∑ b, (R a r * R b s) * ((1/2 : ℝ) * (u a * v b + u b * v a)) := by
  have h₁ : (∑ a, R a r * u a) * (∑ b, R b s * v b) =
      ∑ a, ∑ b, (R a r * R b s) * (u a * v b) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have h₂ : (∑ a, R a s * u a) * (∑ b, R b r * v b) =
      ∑ a, ∑ b, (R a r * R b s) * (u b * v a) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem basis_repr_change {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (b c : Basis (Fin n) ℝ V) (v : V) (r : Fin n) :
    b.repr v r = ∑ a, b.repr (c a) r * c.repr v a := by
  have h := congrArg (fun w => b.repr w r) (c.sum_repr v)
  simpa only [map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, mul_comm] using h.symm

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, Es)

/-- The actual original forward differential is the coordinate coframe
dual to the actual original inverse-chart tangent basis. -/
theorem originalSourceChartDifferential_eq_repr
    (Data : IncrementsOriginalNativeData n d N M P)
    (hA : IsSmoothBufferedAtlas Data.atlas) (i : Fin Data.atlas.count)
    (x : M) (hx : x ∈ (Data.atlas.chart i).source)
    (v : TangentSpace I x) (r : Fin n) :
    incrementsOriginalSourceChartDifferential Data i x v r =
      (bufferedNativeTensorFrame Data.atlas hA i x).repr v r := by
  unfold bufferedNativeTensorFrame
  simp only [dite_eq_left hx, Basis.map_repr, LinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

/-- Both coframe factors, on the same native symmetric bilinear tensor.
The summation is over fixed dimension n, never over atlas labels. -/
theorem original_symmetric_coordinate_tensor_change
    (Data : IncrementsOriginalNativeData n d N M P)
    (hA : IsSmoothBufferedAtlas Data.atlas) (i k : Fin Data.atlas.count)
    (x : M) (hi : x ∈ (Data.atlas.chart i).source)
    (hk : x ∈ (Data.atlas.chart k).source) (r s : Fin n) :
    (incrementsOriginalSymmetricCoordinateTensor Data i x r s).val =
      ∑ a : Fin n, ∑ b : Fin n,
        ((bufferedNativeTensorFrame Data.atlas hA i x).repr
          (bufferedNativeTensorFrame Data.atlas hA k x a) r *
         (bufferedNativeTensorFrame Data.atlas hA i x).repr
          (bufferedNativeTensorFrame Data.atlas hA k x b) s) •
        (incrementsOriginalSymmetricCoordinateTensor Data k x a b).val := by
  classical
  let bi := bufferedNativeTensorFrame Data.atlas hA i x
  let bk := bufferedNativeTensorFrame Data.atlas hA k x
  ext v w
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    repair_original_symmetric_coordinate_tensor_apply]
  simp_rw [originalSourceChartDifferential_eq_repr Data hA i x hi,
    originalSourceChartDifferential_eq_repr Data hA k x hk]
  change (1/2 : ℝ) * (bi.repr v r * bi.repr w s + bi.repr v s * bi.repr w r) = _
  rw [basis_repr_change bi bk v r, basis_repr_change bi bk w s,
    basis_repr_change bi bk v s, basis_repr_change bi bk w r]
  exact symmetric_sum_identity (fun a t => bi.repr (bk a) t)
    (fun a => bk.repr v a) (fun a => bk.repr w a) r s

/-- Exact transformation of the ORIGINAL linear functional.  No arbitrary
extension of its values on symmetric tensors is estimated. -/
theorem original_linear_argument_change
    (Data : IncrementsOriginalNativeData n d N M P)
    (hA : IsSmoothBufferedAtlas Data.atlas) (nu : Fin Data.primaryCount)
    (p : P) (i k : Fin Data.atlas.count)
    (x : M) (hi : x ∈ (Data.atlas.chart i).source)
    (hk : x ∈ (Data.atlas.chart k).source) (r s : Fin n) :
    Data.linearArgument nu p x (incrementsOriginalSymmetricCoordinateTensor Data i x r s).val =
      ∑ a : Fin n, ∑ b : Fin n,
        ((bufferedNativeTensorFrame Data.atlas hA i x).repr
          (bufferedNativeTensorFrame Data.atlas hA k x a) r *
         (bufferedNativeTensorFrame Data.atlas hA i x).repr
          (bufferedNativeTensorFrame Data.atlas hA k x b) s) *
        Data.linearArgument nu p x (incrementsOriginalSymmetricCoordinateTensor Data k x a b).val := by
  rw [original_symmetric_coordinate_tensor_change Data hA i k x hi hk r s]
  simp only [map_sum, map_smul, smul_eq_mul]

end GlobalEmbedding.Continuation.FaithfulIntegration

#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.original_symmetric_coordinate_tensor_change
#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.original_linear_argument_change

