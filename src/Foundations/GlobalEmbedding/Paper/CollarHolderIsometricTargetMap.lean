import GlobalEmbedding.Paper.CollarHolderTargetMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual full-norm isometric target inclusions of little Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 524–534. The actual real contraction ball must retain its original norm.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- An actual linear isometry of finite real Euclidean values induces an actual linear
isometry of the original little Hölder spaces, with exactly its pointwise target action.

Source: Proposition `prop:collar`, proof lines 524–534, norm-preserving real forms.
The proved actual target-map theorem gives a little-space map of norm at most one. The
adjoint of the value isometry is a left inverse and also has norm at most one, including
zero-dimensional spaces. Its actual target map is a left inverse on little functions by
underlying-function injectivity. The two contraction inequalities force equality of the
full original Hölder norms. No alternate norm or missing top quotient is used. -/
theorem collar_holder_isometric_target_map {a N M k : ℕ} {α : ℝ}
    (A : EuclideanSpace ℝ (Fin N) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin M)) :
    ∃ L : LittlePeriodicCAlphaFunction a N k α →ₗᵢ[ℝ]
        LittlePeriodicCAlphaFunction a M k α,
      ∀ f, (L f : PeriodicCAlphaFunction a M k α).toFun =
        A ∘ (f : PeriodicCAlphaFunction a N k α).toFun := by
  obtain ⟨_, L, _, _, hL, hLn⟩ := collar_holder_target_map (a := a) (k := k) (α := α)
    A.toContinuousLinearMap
  obtain ⟨_, R, _, _, hR, hRn⟩ := collar_holder_target_map (a := a) (k := k) (α := α)
    (ContinuousLinearMap.adjoint A.toContinuousLinearMap)
  have hL1 : ‖L‖ ≤ 1 := hLn.trans A.norm_toContinuousLinearMap_le
  have hR1 : ‖R‖ ≤ 1 := hRn.trans (by
    simpa only [LinearIsometryEquiv.norm_map] using A.norm_toContinuousLinearMap_le)
  have hleft (f : LittlePeriodicCAlphaFunction a N k α) : R (L f) = f := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    rw [hR, Function.comp_apply, hL, Function.comp_apply]
    have he := congrArg (fun T : EuclideanSpace ℝ (Fin N) →L[ℝ]
        EuclideanSpace ℝ (Fin N) ↦ T (f.val.toFun x)) A.adjoint_comp_self
    exact he
  have hnorm (f : LittlePeriodicCAlphaFunction a N k α) : ‖L f‖ = ‖f‖ := by
    apply le_antisymm
    · exact (L.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg f) hL1)
    · calc
        _ = ‖R (L f)‖ := congrArg norm (hleft f).symm
        _ ≤ ‖R‖ * ‖L f‖ := R.le_opNorm (L f)
        _ ≤ ‖L f‖ := mul_le_of_le_one_left (norm_nonneg (L f)) hR1
  exact ⟨{ toLinearMap := L.toLinearMap, norm_map' := hnorm }, hL⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_isometric_target_map
