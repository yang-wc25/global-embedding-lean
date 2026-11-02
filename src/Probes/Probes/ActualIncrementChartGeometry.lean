import GlobalEmbedding.Paper.IncrementsModeCoordinateRegularity
import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame

/-!
# Actual increment geometry in the chosen maximal chart

These are pointwise identities for the original `normalSpace` and
`incrementsModeSecondForm`, in an arbitrary chosen maximal chart. They expose
the chart identities used internally by the original joint-geometry proof so
that quantitative joint bounds can be transferred by actual open-domain germs.
No second-form, projection, chart derivative, or reserve bound is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The true normal space equals the orthogonal complement of the actual
coordinate first derivative in the same chosen maximal chart. -/
theorem actual_increment_normalSpace_eq_chart_range
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target) :
    normalSpace (I := 𝓙) F (e.symm x) =
      (LinearMap.range (fderiv ℝ (F ∘ e.symm) x).toLinearMap)ᗮ := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hec : e.MDifferentiable 𝓙 𝓙 := by
    constructor
    · intro q hq
      exact (mdifferentiableAt_of_mem_maximalAtlas he1 hq).mdifferentiableWithinAt
    · intro q hq
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hq).mdifferentiableWithinAt
  have hpush : fderiv ℝ (F ∘ e.symm) x =
      ((tangentSpaceCastModel 𝓘(ℝ, V) (F (e.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, V) F (e.symm x))).comp
          (mfderiv 𝓙 𝓙 e.symm x) := by
    have hc := hec.mdifferentiableAt_symm hx
    have h := mfderiv_comp x (hF.mdifferentiable (by simp) _) hc
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ tangentSpaceCastModel 𝓘(ℝ, V) (F (e.symm x))
      (L ((tangentSpaceCastModel 𝓙 x).symm v))) h
  rw [hpush]
  unfold normalSpace
  congr 1
  let R := (tangentSpaceCastModel 𝓘(ℝ, V) (F (e.symm x))).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ, V) F (e.symm x))
  let C : D →L[ℝ] TangentSpace 𝓙 (e.symm x) := mfderiv 𝓙 𝓙 e.symm x
  have hC : Function.Surjective C := (hec.symm.mfderiv hx).surjective
  have hr := LinearMap.range_comp C.toLinearMap R.toLinearMap
  rw [LinearMap.range_eq_top.mpr hC, Submodule.map_top] at hr
  exact hr.symm

/-- Every original true-B row is the true normal projection of the actual
coordinate Hessian; both slots remain the original coordinate directions. -/
theorem actual_increment_secondForm_chart
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target) (i j : Fin (m + 1)) :
    (incrementsModeSecondForm (I := 𝓙) F hF e.symm x i j : V) =
      (normalSpace (I := 𝓙) F (e.symm x)).starProjection
        (fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have he2 : e ∈ IsManifold.maximalAtlas 𝓙 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hec : e.MDifferentiable 𝓙 𝓙 := by
    constructor
    · intro q hq
      exact (mdifferentiableAt_of_mem_maximalAtlas he1 hq).mdifferentiableWithinAt
    · intro q hq
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hq).mdifferentiableWithinAt
  have hcv (k : Fin (m + 1)) : mfderiv 𝓙 𝓙 e (e.symm x)
      (incrementsModeCoordinateDirections (I := 𝓙) e.symm x k) =
        EuclideanSpace.single k 1 := by
    change mfderiv 𝓙 𝓙 e (e.symm x)
      (mfderiv 𝓙 𝓙 e.symm x (EuclideanSpace.single k 1)) = _
    exact congrArg (fun L ↦ L (EuclideanSpace.single k 1)) (hec.comp_symm_deriv hx)
  dsimp only [incrementsModeSecondForm]
  rw [← trueSecondForm_chart F hF (e.symm x) e he2 (e.map_target hx)]
  change (normalSpace (I := 𝓙) F (e.symm x)).starProjection
    (fderiv ℝ (fderiv ℝ (F ∘ e.symm)) (e (e.symm x))
      (mfderiv 𝓙 𝓙 e (e.symm x) (incrementsModeCoordinateDirections (I := 𝓙) e.symm x i))
      (mfderiv 𝓙 𝓙 e (e.symm x) (incrementsModeCoordinateDirections (I := 𝓙) e.symm x j))) = _
  rw [hcv i, hcv j, e.right_inv hx]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_normalSpace_eq_chart_range
#print axioms GlobalEmbedding.Continuation.actual_increment_secondForm_chart
