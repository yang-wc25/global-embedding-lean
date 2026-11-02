import NormalPolar.CompressionResponseChain

/-!
# The true compression response retains the actual projection gap

For genuine orthogonal projections the compression identity
G-I=-compression((P-R)^2) holds on the entire actual family. Its native
derivative therefore has the additional projection-gap factor. No bound on
the compression derivative is an input.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]

private noncomputable local instance defectResponseAmbientSemi :
    SeminormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance defectResponseAmbientNorm :
    NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance defectResponseAmbientSpace :
    NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance defectResponseFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance defectResponseFiberNorm (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance defectResponseFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

/-- The actual squared-defect derivative has its genuine quadratic-response
size; no commutation of the defect and its variation is asserted. -/
theorem norm_fderiv_projectionDefect_right_apply_le
    (P : V →L[ℝ] V) (R : X → V →L[ℝ] V) (u a : X)
    (hR : DifferentiableAt ℝ R u) :
    ‖fderiv ℝ (fun z ↦ projectionDefect P (R z)) u a‖ ≤
      2 * ‖P - R u‖ * ‖fderiv ℝ R u a‖ := by
  rw [fderiv_projectionDefect_right_apply P R u a hR, norm_neg]
  calc
    _ ≤ ‖(P - R u) * (fderiv ℝ R u a)‖ +
        ‖(fderiv ℝ R u a) * (P - R u)‖ := norm_add_le _ _
    _ ≤ ‖P - R u‖ * ‖fderiv ℝ R u a‖ +
        ‖fderiv ℝ R u a‖ * ‖P - R u‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- The same actual compression is identity minus the compressed squared
defect. This exact family identity is differentiated in the next theorem. -/
theorem normalProjectionCompression_eq_one_sub_defect
    (K L : Submodule ℝ V) :
    normalProjectionCompression K L.starProjection =
      1 - normalProjectionCompression K (projectionDefect K.starProjection L.starProjection) := by
  have h := normalProjectionCompression_sub_one_eq_defect K L
  calc
    _ = (normalProjectionCompression K L.starProjection - 1) + 1 := by abel
    _ = -normalProjectionCompression K (projectionDefect K.starProjection L.starProjection) + 1 := by rw [h]
    _ = _ := by abel

/-- The true compression's native response is minus the compressed squared
defect response. This uses the actual projection identity for each family
member, rather than an abstract budget for DG. -/
theorem fderiv_actualNormalCompression_eq_negative_defect
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u) :
    fderiv ℝ (fun z ↦ normalProjectionCompression K (L z).starProjection) u a =
      -normalProjectionCompression K
        (fderiv ℝ (fun z ↦ projectionDefect K.starProjection (L z).starProjection) u a) := by
  have hE := differentiableAt_projectionDefect_right K.starProjection
    (fun z ↦ (L z).starProjection) u hR
  have hcomp := (normalProjectionCompressionL K).hasFDerivAt.comp u hE.hasFDerivAt
  change HasFDerivAt
    (fun z ↦ normalProjectionCompression K (projectionDefect K.starProjection (L z).starProjection)) _ u at hcomp
  have h := (hasFDerivAt_const (1 : K →L[ℝ] K) u).sub hcomp
  have heq : (fun z ↦ normalProjectionCompression K (L z).starProjection) =
      (fun _ : X ↦ (1 : K →L[ℝ] K)) -
        (fun z ↦ normalProjectionCompression K (projectionDefect K.starProjection (L z).starProjection)) := by
    funext z
    exact normalProjectionCompression_eq_one_sub_defect K (L z)
  rw [heq]
  have hderivative := congrArg (fun D : X →L[ℝ] K →L[ℝ] K ↦ D a) h.fderiv
  have hcompress (A : V →L[ℝ] V) :
      (normalProjectionCompressionL K) A = normalProjectionCompression K A := rfl
  simpa only [ContinuousLinearMap.comp_apply, sub_apply, zero_apply, zero_sub, neg_apply,
    hcompress] using hderivative

/-- The genuine DG response is O(gap times DR), including a zero-dimensional
old normal fiber. The factor 2 comes from the two actual product-rule terms. -/
theorem norm_fderiv_actualNormalCompression_apply_le_gap
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u) :
    ‖fderiv ℝ (fun z ↦ normalProjectionCompression K (L z).starProjection) u a‖ ≤
      2 * ‖K.starProjection - (L u).starProjection‖ *
        ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  rw [fderiv_actualNormalCompression_eq_negative_defect K L u a hR, norm_neg]
  exact (normalProjectionCompression_norm_le K _).trans
    (norm_fderiv_projectionDefect_right_apply_le K.starProjection
      (fun z ↦ (L z).starProjection) u a hR)

end GlobalEmbedding.NormalPolar
