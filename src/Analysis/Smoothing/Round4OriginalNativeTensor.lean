import Probes.ActualCoreWeightedJets
import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import GlobalEmbedding.Offline.ContinuousRankOneBasis

/-! The original ordered tensor coordinates reconstruct exactly the genuine
native tensor pulled back by the actual inverse-chart differential. The
fixed coordinate-to-bilinear map is explicit and depends only on dimension.
No unrelated matrix field or Riemannian norm comparison is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation



private local instance nativeTensorNormed (n : ℕ) :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := inferInstance
private local instance nativeTensorSpace (n : ℕ) :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := inferInstance

def round4NativeTensorFromCoordinates (n : ℕ) :
    (Fin (n*n) → ℝ) →L[ℝ] ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) :=
  ∑ r : Fin n, ∑ s : Fin n,
    (ContinuousLinearMap.proj (finProdFinEquiv (r,s)) : (Fin (n*n) → ℝ) →L[ℝ] ℝ).smulRight
      ((EuclideanSpace.proj r).smulRight (EuclideanSpace.proj s))

@[simp] theorem round4NativeTensorFromCoordinates_apply (n : ℕ)
    (a : Fin (n*n) → ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    round4NativeTensorFromCoordinates n a v w =
      ∑ r : Fin n, ∑ s : Fin n, a (finProdFinEquiv (r,s))*v r*w s := by
  simp [round4NativeTensorFromCoordinates,ContinuousLinearMap.smulRight_apply,smul_eq_mul,mul_assoc]

@[simp] theorem round4NativeTensorFromCoordinates_basis (n : ℕ)
    (a : Fin (n*n) → ℝ) (r s : Fin n) :
    round4NativeTensorFromCoordinates n a (EuclideanSpace.single r 1) (EuclideanSpace.single s 1) =
      a (finProdFinEquiv (r,s)) := by
  simp [round4NativeTensorFromCoordinates_apply,PiLp.single_apply]

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "X" => (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin n))
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))

def round4OriginalNativeTensorCoordinates
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin c) (z : X) : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  round4NativeTensorFromCoordinates n
    (incrementsOriginalTensorCoordinates A B T i (parameterTensorModelEquiv n d z))

/-- This equality uses the exact original source vectors, with both true
inverse-chart derivatives. It is valid before any tensor norm estimates. -/
theorem round4_original_tensor_coordinates_pullback
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin c) (y : Fin (n+d) → ℝ) :
    let x := incrementsOriginalJointPoint A B i y
    let J := (mfderiv 𝓙 𝓙 (A.chart i.1).symm (incrementsOriginalSourcePoint y)).comp
      (tangentSpaceCastModel 𝓙 (incrementsOriginalSourcePoint y)).symm.toContinuousLinearMap
    continuousBilinearForget
      (round4NativeTensorFromCoordinates n (incrementsOriginalTensorCoordinates A B T i y)) =
      (T x.1 x.2).comp J.toLinearMap J.toLinearMap := by
  intro x J
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro r
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro s
  simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,continuousBilinearForget_apply,
    round4NativeTensorFromCoordinates_basis,incrementsOriginalTensorCoordinates,
    Equiv.symm_apply_apply] using
    (show T x.1 x.2 (incrementsOriginalSourceVector A i.1 y r)
      (incrementsOriginalSourceVector A i.1 y s) = (T x.1 x.2).comp J.toLinearMap J.toLinearMap
        (EuclideanSpace.single r 1) (EuclideanSpace.single s 1) from rfl)

theorem round4_original_native_tensor_isSymm
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin c) (z : X)
    (hT : (T (incrementsOriginalJointPoint A B i (parameterTensorModelEquiv n d z)).1
      (incrementsOriginalJointPoint A B i (parameterTensorModelEquiv n d z)).2).IsSymm) :
    ∀ v w, round4OriginalNativeTensorCoordinates A B T i z v w =
      round4OriginalNativeTensorCoordinates A B T i z w v := by
  intro v w
  have he := round4_original_tensor_coordinates_pullback A B T i (parameterTensorModelEquiv n d z)
  have hvw := congrArg (fun Q : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) => Q v w) he
  have hwv := congrArg (fun Q : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) => Q w v) he
  exact hvw.trans ((hT.eq _ _).trans hwv.symm)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_tensor_coordinates_pullback
#print axioms GlobalEmbedding.Continuation.round4_original_native_tensor_isSymm
