import GlobalEmbedding.Paper.FrameCrossProjectionNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, quantitative zero-order normal-projection continuity. -/

namespace GlobalEmbedding.Paper

/-- Two coercive frames have normal projections whose operator distance is controlled
by their frame distance and reciprocal lower bounds.

Proof: write P_B−P_A=P_B Q_A−Q_B P_A. The first cross term is bounded by the
preceding theorem. The adjoint of the second cross term is P_A Q_B, which has the
opposite bound because both orthogonal projections are symmetric. Adjoint preserves
operator norm. Add the two bounds.
Source: `prop:initialization`, quantitative elliptic normal-projection continuity. -/
theorem frame_normal_projection_gap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (A B : E →L[ℝ] F) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖) (hB : ∀ v, b * ‖v‖ ≤ ‖B v‖) :
    ‖(LinearMap.range B.toLinearMap)ᗮ.starProjection -
      (LinearMap.range A.toLinearMap)ᗮ.starProjection‖ ≤ ‖A - B‖ * (1 / a + 1 / b) := by
  let KA := LinearMap.range A.toLinearMap
  let KB := LinearMap.range B.toLinearMap
  have h1 := frame_cross_projection_norm A B a ha hA
  have h2 := frame_cross_projection_norm B A b hb hB
  have ht : ‖KB.starProjection.comp KAᗮ.starProjection‖ =
      ‖KAᗮ.starProjection.comp KB.starProjection‖ := by
    have hnorm := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := F) (F := F)).norm_map
      (KB.starProjection.comp KAᗮ.starProjection)
    simpa only [ContinuousLinearMap.adjoint_comp,
      KAᗮ.starProjection_isSymmetric.clm_adjoint_eq,
      KB.starProjection_isSymmetric.clm_adjoint_eq] using hnorm.symm
  have heq : KBᗮ.starProjection - KAᗮ.starProjection =
      KBᗮ.starProjection.comp KA.starProjection -
        KB.starProjection.comp KAᗮ.starProjection := by
    ext z
    simp only [Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖KBᗮ.starProjection.comp KA.starProjection‖ +
        ‖KB.starProjection.comp KAᗮ.starProjection‖ := norm_sub_le _ _
    _ = ‖KBᗮ.starProjection.comp KA.starProjection‖ +
        ‖KAᗮ.starProjection.comp KB.starProjection‖ := by rw [ht]
    _ ≤ ‖A - B‖ / a + ‖B - A‖ / b := add_le_add h1 h2
    _ = ‖A - B‖ * (1 / a + 1 / b) := by rw [norm_sub_rev B A]; ring

end GlobalEmbedding.Paper
