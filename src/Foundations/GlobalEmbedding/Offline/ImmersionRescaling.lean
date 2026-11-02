import GlobalEmbedding.Paper.InducedMetric
import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.TrueSecondFormEvaluation
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Nonzero constant rescaling of the actual immersion geometry

Source: `literature/parallelizable-stable-plus-one/main.tex`,
`cor:small-immersion`, proof, and the original DAG node `immersion-rescaling`.

This candidate uses the original `inducedMetric`, `normalSpace`, `trueSecondForm`,
`GoodCovector`, and `PhaseRegular` definitions. The second-form identity is stated
after the original normal inclusions into the same ambient Euclidean space, so it
does not replace the normal bundle by a new carrier. Scalars may be negative.

This is an isolated offline candidate, not a claim of main-library acceptance.
-/

noncomputable section

open Manifold
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Offline

open GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

/-- Differentiation of the same map after constant ambient scalar multiplication.
Proof: the native manifold derivative rule for constant scalar multiplication.
Source: `immersion-rescaling`, first derivative identity. -/
theorem mfderiv_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (x : M) :
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (c • F) x =
      c • mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x := by
  exact const_smul_mfderiv ((hF x).mdifferentiableAt (by simp)) c

/-- Smoothness of the same scalar-multiplied Euclidean map.
Proof: the native jointly smooth scalar action composed with a constant and `F`.
Source: `immersion-rescaling`. -/
theorem contMDiff_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (c • F) := by
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ c) := contMDiff_const
  exact hconst.smul hF

/-- The derivative identity with the actual target-tangent casts used by the
original metric and normal-space definitions. Proof: pointwise evaluation of the
manifold derivative identity. Source: `immersion-rescaling`. -/
theorem ambientDerivative_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (x : M) :
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ((c • F) x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (c • F) x) =
      c • (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun (mfderiv_const_rescale F hF c x) v

/-- The literal induced bilinear form scales by `c²`.
Proof: differentiate the scalar multiple and use both real-inner-product scalar
identities. This assertion also includes `c=0`.
Source: `cor:small-immersion`, the final exact-metric rescaling. -/
theorem inducedMetric_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (x : M) :
    inducedMetric (I := I) (c • F) x = c ^ 2 • inducedMetric (I := I) F x := by
  unfold inducedMetric
  rw [ambientDerivative_const_rescale F hF]
  ext v w
  simp only [LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe,
    smul_apply, innerₗ_apply_apply, real_inner_smul_left,
    real_inner_smul_right, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Nonzero ambient rescaling preserves the actual normal submodule.
Proof: the derivative is multiplied by a nonzero scalar, so its range is the same
linear subspace; take the orthogonal complement. No global normal frame is used.
Source: `immersion-rescaling`, tangent and normal-space equality. -/
theorem normalSpace_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) :
    normalSpace (I := I) (c • F) x = normalSpace (I := I) F x := by
  unfold normalSpace
  rw [ambientDerivative_const_rescale F hF]
  rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ c hc]

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- The actual entire symmetric-square second form scales by `c`, after the
original normal inclusions into Euclidean space.

Proof: on every quotient product, `trueSecondForm_product` identifies the map with
the centered coordinate Hessian followed by normal projection. The original
normal submodules agree by `normalSpace_const_rescale`. Two applications of the
native scalar derivative identity scale the Hessian by `c`; linearity of the same
projection finishes. Quotient and tensor extensionality give equality on all of
the original binary symmetric square, with no normalization change.
Source: `immersion-rescaling`, the actual second-form identity. -/
theorem trueSecondForm_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) :
    (normalSpace (I := I) (c • F) x).subtype.comp
        (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x) =
      c • (normalSpace (I := I) F x).subtype.comp (trueSecondForm F hF x) := by
  apply (symmetricSquareRelations (TangentSpace I x)).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
      (symmetricSquareProduct (TangentSpace I x) v w) : EuclideanSpace ℝ (Fin N)) =
    c • (trueSecondForm F hF x
      (symmetricSquareProduct (TangentSpace I x) v w) : EuclideanSpace ℝ (Fin N))
  rw [trueSecondForm_product, trueSecondForm_product]
  change (normalSpace (I := I) (c • F) x).starProjection
      (fderiv ℝ (fderiv ℝ ((c • F) ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)) =
    c • (normalSpace (I := I) F x).starProjection
      (fderiv ℝ (fderiv ℝ (F ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w))
  rw [normalSpace_const_rescale F hF c hc]
  have hcomp : (c • F) ∘ (extChartAt I x).symm =
      c • (F ∘ (extChartAt I x).symm) := rfl
  rw [hcomp, fderiv_const_smul_field (𝕜 := ℝ) (f := F ∘ (extChartAt I x).symm) c]
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (F ∘ (extChartAt I x).symm)) c]
  simp only [Pi.smul_apply, smul_apply, map_smul]

/-- Every original good covector remains good after a nonzero constant rescaling.
The converse holds too, since the ambient inclusion is injective and the true
second form is multiplied by a nonzero scalar on the exact same kernel square.
Source: `immersion-rescaling`, preservation of all good covectors. -/
theorem goodCovector_const_rescale_iff
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    GoodCovector (c • F) (contMDiff_const_rescale F hF c) x ξ ↔ GoodCovector F hF x ξ := by
  have hB (q : SymmetricSquare (TangentSpace I x)) :
      (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x q : EuclideanSpace ℝ (Fin N)) =
        c • (trueSecondForm F hF x q : EuclideanSpace ℝ (Fin N)) :=
    DFunLike.congr_fun (trueSecondForm_const_rescale F hF c hc x) q
  constructor
  · rintro ⟨hξ, hinj⟩
    refine ⟨hξ, ?_⟩
    intro u v huv
    apply hinj
    apply Subtype.ext
    change (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
        (symmetricSquareLinearMap ξ.ker.subtype u) : EuclideanSpace ℝ (Fin N)) =
      (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
        (symmetricSquareLinearMap ξ.ker.subtype v) : EuclideanSpace ℝ (Fin N))
    rw [hB, hB]
    exact congrArg (fun z : normalSpace (I := I) F x ↦ c • (z : EuclideanSpace ℝ (Fin N))) huv
  · rintro ⟨hξ, hinj⟩
    refine ⟨hξ, ?_⟩
    intro u v huv
    apply hinj
    apply Subtype.ext
    have h := congrArg (fun z : normalSpace (I := I) (c • F) x ↦
      (z : EuclideanSpace ℝ (Fin N))) huv
    change (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
        (symmetricSquareLinearMap ξ.ker.subtype u) : EuclideanSpace ℝ (Fin N)) =
      (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) x
        (symmetricSquareLinearMap ξ.ker.subtype v) : EuclideanSpace ℝ (Fin N)) at h
    rw [hB, hB] at h
    exact (smul_right_injective _ hc) h

/-- The original phase-regularity predicate is invariant under every nonzero
constant ambient scalar, including negative scalars. Proof: the good-covector
equivalence applies pointwise without choosing a global covector field.
Source: `cor:small-immersion`, preservation of phase regularity. -/
theorem phaseRegular_const_rescale_iff
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (hc : c ≠ 0) :
    PhaseRegular (c • F) (contMDiff_const_rescale F hF c) ↔ PhaseRegular F hF := by
  constructor <;> intro h x
  · obtain ⟨ξ, hξ⟩ := h x
    exact ⟨ξ, (goodCovector_const_rescale_iff F hF c hc x ξ).mp hξ⟩
  · obtain ⟨ξ, hξ⟩ := h x
    exact ⟨ξ, (goodCovector_const_rescale_iff F hF c hc x ξ).mpr hξ⟩

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- Nonzero constant rescaling preserves injectivity of the actual differential.
Proof: scalar multiplication by `c≠0` is injective, and the differential scales by
`c`. Source: `immersion-rescaling`, preservation of immersion. -/
theorem immersion_const_rescale_iff
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (x : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (c • F) x) ↔
      Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x) := by
  rw [mfderiv_const_rescale F hF]
  constructor
  · intro h u v huv
    exact h (congrArg (fun z : EuclideanSpace ℝ (Fin N) ↦ c • z) huv)
  · intro h u v huv
    exact h ((smul_right_injective _ hc) huv)

omit [TopologicalSpace M] in
/-- Pointwise Euclidean size of the very same rescaled map.
Proof: absolute homogeneity of the native norm.
Source: `cor:small-immersion`, the final image-radius bound. -/
theorem norm_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N)) (c : ℝ) (x : M) :
    ‖(c • F) x‖ = |c| * ‖F x‖ := by
  exact norm_smul c (F x)

/-- The complete original rescaling statement for a phase-regular immersion.
All geometric conclusions refer to the original map and original predicates.
Proof: combine smooth scalar multiplication with the actual differential,
phase, metric, and norm identities proved above.
Source: the complete original DAG node `immersion-rescaling`. -/
theorem phaseRegular_immersion_const_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ x, Function.Injective
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))
    (hphase : PhaseRegular F hF) (c : ℝ) (hc : c ≠ 0) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (c • F) ∧
    (∀ x, Function.Injective
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (c • F) x)) ∧
    PhaseRegular (c • F) (contMDiff_const_rescale F hF c) ∧
    (∀ x, inducedMetric (I := I) (c • F) x = c ^ 2 • inducedMetric (I := I) F x) ∧
    (∀ x, ‖(c • F) x‖ = |c| * ‖F x‖) := by
  exact ⟨contMDiff_const_rescale F hF c,
    fun x ↦ (immersion_const_rescale_iff F hF c hc x).mpr (himm x),
    (phaseRegular_const_rescale_iff F hF c hc).mpr hphase,
    inducedMetric_const_rescale F hF c, norm_const_rescale F c⟩

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- Exact cancellation of the target metric scaling used in the small-immersion
corollary. The input metric is an arbitrary actual bilinear-form field.
Proof: the two scalar squares multiply to one.
Source: `cor:small-immersion`, `F = H_*/T`. -/
theorem inducedMetric_inverse_rescale
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (T : ℝ) (hT : T ≠ 0)
    (hmetric : ∀ x, inducedMetric (I := I) F x = T ^ 2 • g x) :
    ∀ x, inducedMetric (I := I) (T⁻¹ • F) x = g x := by
  intro x
  rw [inducedMetric_const_rescale F hF, hmetric, smul_smul,
    ← mul_pow, inv_mul_cancel₀ hT, one_pow, one_smul]

omit [TopologicalSpace M] in
/-- The strict pointwise image-radius bound for the same inverse rescaling.
Proof: divide the original uniform bound by the positive scale. This does not
require the source to be nonempty, compact, connected, or oriented.
Source: `cor:small-immersion`, `sup |F| < r` after increasing `T`. -/
theorem norm_inverse_rescale_lt
    (F : M → EuclideanSpace ℝ (Fin N)) (C T r : ℝ)
    (hT : 0 < T) (hbound : ∀ x, ‖F x‖ ≤ C) (hsmall : C < r * T) :
    ∀ x, ‖(T⁻¹ • F) x‖ < r := by
  intro x
  calc
    ‖(T⁻¹ • F) x‖ = ‖F x‖ / T := by
      rw [norm_const_rescale, abs_of_pos (inv_pos.mpr hT), div_eq_mul_inv, mul_comm]
    _ ≤ C / T := div_le_div_of_nonneg_right (hbound x) hT.le
    _ < r := (div_lt_iff₀ hT).mpr hsmall

#print axioms contMDiff_const_rescale
#print axioms ambientDerivative_const_rescale
#print axioms mfderiv_const_rescale
#print axioms inducedMetric_const_rescale
#print axioms normalSpace_const_rescale
#print axioms trueSecondForm_const_rescale
#print axioms goodCovector_const_rescale_iff
#print axioms phaseRegular_const_rescale_iff
#print axioms immersion_const_rescale_iff
#print axioms norm_const_rescale
#print axioms phaseRegular_immersion_const_rescale
#print axioms inducedMetric_inverse_rescale
#print axioms norm_inverse_rescale_lt

end GlobalEmbedding.Offline
