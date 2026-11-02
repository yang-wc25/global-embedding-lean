import Upgrade.RankQSchur

/-!
# Differential of the actual Schur residual

The derivative at the reference form is its literal kernel-to-normal block.
The inverse and both off-diagonal blocks are retained in the nearby residual;
only their reference product derivative vanishes. This is the geometric input
needed to push the actual probe response through the rank equation (10.1).
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The continuous linear map sending a perturbation to its actual normal block. -/
def rankQNormalBlock (B : S →L[ℝ] W) :
    (S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ) :=
  (ContinuousLinearMap.compL ℝ B.ker W B.rangeᗮ
    B.rangeᗮ.orthogonalProjectionOnto).comp
      ((ContinuousLinearMap.compL ℝ B.ker S W).flip B.ker.subtypeL)

@[simp] theorem rankQNormalBlock_apply (B C : S →L[ℝ] W) :
    rankQNormalBlock B C = rankQBlockD B C := rfl

/-- The exact derivative, with no desired-rank hypothesis. -/
theorem rankQSchur_hasFDerivAt_self (B : S →L[ℝ] W) :
    HasFDerivAt (rankQSchur B) (rankQNormalBlock B) B := by
  have hd : HasFDerivAt (rankQBlockD B) (rankQNormalBlock B) B :=
    (rankQNormalBlock B).hasFDerivAt
  have hm : HasFDerivAt (rankQBlockM B) (fderiv ℝ (rankQBlockM B) B) B :=
    ((rankQBlockM_contDiff B).differentiable (by simp) B).hasFDerivAt
  have hn : HasFDerivAt (rankQBlockN B) (fderiv ℝ (rankQBlockN B) B) B :=
    ((rankQBlockN_contDiff B).differentiable (by simp) B).hasFDerivAt
  have hi : DifferentiableAt ℝ (fun C ↦ (rankQBlockA B C).inverse) B := by
    have hc : ContDiffAt ℝ ∞ (fun C ↦ (rankQBlockA B C).inverse) B := by
      have hA : (rankQBlockA B B).IsInvertible := by
        rw [rankQBlockA_self]
        exact ⟨ContinuousLinearEquiv.refl ℝ B.range, rfl⟩
      exact hA.contDiffAt_map_inverse.comp B (rankQBlockA_contDiff B).contDiffAt
    exact hc.differentiableAt (by simp)
  have hzero : HasFDerivAt
      (fun C ↦ (rankQBlockM B C).comp
        ((rankQBlockA B C).inverse.comp (rankQBlockN B C)))
      (0 : (S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.rangeᗮ)) B := by
    simpa [rankQBlockM_self, rankQBlockN_self] using
      hm.clm_comp (hi.hasFDerivAt.clm_comp hn)
  change HasFDerivAt
    (fun C ↦ rankQBlockD B C - (rankQBlockM B C).comp
      ((rankQBlockA B C).inverse.comp (rankQBlockN B C))) (rankQNormalBlock B) B
  have hall := HasFDerivAt.sub (𝕜 := ℝ) (E := S →L[ℝ] W)
    (F := B.ker →L[ℝ] B.rangeᗮ) hd hzero
  simpa only [sub_zero] using! hall


@[simp] theorem rankQSchur_fderiv_self (B : S →L[ℝ] W) :
    fderiv ℝ (rankQSchur B) B = rankQNormalBlock B :=
  (rankQSchur_hasFDerivAt_self B).fderiv

/-- The chosen block stays invertible on a genuine neighborhood of the original form. -/
theorem rankQBlockA_eventually_isInvertible (B : S →L[ℝ] W) :
    ∀ᶠ C in 𝓝 B, (rankQBlockA B C).IsInvertible := by
  have hA : (rankQBlockA B B).IsInvertible := by
    rw [rankQBlockA_self]
    exact ⟨ContinuousLinearEquiv.refl ℝ B.range, rfl⟩
  exact (rankQBlockA_contDiff B).continuous.continuousAt.preimage_mem_nhds
    hA.eventually_nhds

/-- In the fixed chart the derivative of the actual residual varies continuously. -/
theorem rankQSchur_continuousAt_fderiv (B : S →L[ℝ] W) :
    ContinuousAt (fderiv ℝ (rankQSchur B)) B :=
  (rankQSchur_contDiffAt_self B).continuousAt_fderiv (by simp)

end GlobalEmbedding.Upgrade
