import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, quantitative zero-order normal-projection continuity. -/

namespace GlobalEmbedding.Paper

/-- A normal projection of B applied to the tangent projection of A is controlled by
frame distance divided by the lower bound of A.

Proof: represent the tangent projection as Av. Coercivity bounds v, while the B-normal
projection kills Bv, leaving the projection of (A−B)v. Use projection contractivity.
Source: `prop:initialization`, uniform zero-order normal-projection comparison. -/
theorem frame_cross_projection_norm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A B : E →L[ℝ] F) (a : ℝ) (ha : 0 < a)
    (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖) :
    ‖(LinearMap.range B.toLinearMap)ᗮ.starProjection.comp
      (LinearMap.range A.toLinearMap).starProjection‖ ≤ ‖A - B‖ / a := by
  let KA := LinearMap.range A.toLinearMap
  let KB := LinearMap.range B.toLinearMap
  have hzero : ∀ v : E, KBᗮ.starProjection (B v) = 0 := by
    intro v
    change B v ∈ KBᗮ.starProjection.ker
    rw [Submodule.ker_starProjection]
    exact Submodule.le_orthogonal_orthogonal KB (show B v ∈ KB from ⟨v, rfl⟩)
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) ha.le)
  intro z
  obtain ⟨v, hv⟩ := (KA.starProjection_apply_mem z)
  change A v = KA.starProjection z at hv
  have hAv : ‖A v‖ ≤ ‖z‖ := by
    rw [hv]
    exact KA.norm_starProjection_apply_le z
  have hvl : ‖v‖ ≤ ‖z‖ / a := by
    apply (le_div_iff₀ ha).mpr
    have hl := hA v
    nlinarith
  have heq : KBᗮ.starProjection (KA.starProjection z) = KBᗮ.starProjection ((A - B) v) := by
    rw [← hv]
    simp only [sub_apply, map_sub, hzero, sub_zero]
  calc
    ‖(KBᗮ.starProjection.comp KA.starProjection) z‖ =
        ‖KBᗮ.starProjection ((A - B) v)‖ := congrArg norm heq
    _ ≤ ‖(A - B) v‖ := KBᗮ.norm_starProjection_apply_le _
    _ ≤ ‖A - B‖ * ‖v‖ := (A - B).le_opNorm v
    _ ≤ ‖A - B‖ * (‖z‖ / a) := mul_le_mul_of_nonneg_left hvl (norm_nonneg _)
    _ = (‖A - B‖ / a) * ‖z‖ := by ring

end GlobalEmbedding.Paper
