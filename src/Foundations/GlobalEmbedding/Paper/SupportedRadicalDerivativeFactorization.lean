import GlobalEmbedding.Paper.SupportedRadicalNormalResidual

/-!
# The SAME normal derivative depends only on actual evaluation at the radical

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1009–1012 and 1018–1022. The proved full derivative formula determines its own
factorization through the mixed projection once that projection is proved to preserve
actual evaluation. No desired differential or normal-rank equality is assumed.
-/

noncomputable section
namespace GlobalEmbedding.Paper

variable {K U H Z : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Equal genuine operator evaluations at the original radical give equal actual normal
residual derivatives. The scalar rows are recovered by the SAME row equivalence.
Source: `prop:supported-rank`, projection to the actual mixed normal component. -/
theorem supportedRadicalNormalResidual_fderiv_evaluation_congr
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (Δ₁ Δ₂ : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (hΔ : ∀ k, Δ₁ k (1, 0) = Δ₂ k (1, 0)) :
    fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q Δ₁ =
      fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q Δ₂ := by
  have hrows : supportedRadicalRows a r Δ₁ (1, 0) =
      supportedRadicalRows a r Δ₂ (1, 0) := by
    apply a.injective
    apply ContinuousLinearMap.ext
    intro k
    rw [supportedRadicalRows_apply, supportedRadicalRows_apply, hΔ k]
  apply ContinuousLinearMap.ext
  intro k
  apply Subtype.ext
  rw [supportedRadicalNormalResidual_fderiv_apply a r w hw Q e hA hC Δ₁ k,
    supportedRadicalNormalResidual_fderiv_apply a r w hw Q e hA hC Δ₂ k,
    hΔ k, hrows]

/-- Projection preserving the ACTUAL evaluation yields the actual derivative factorization.
In the original consumer P is the genuine orthogonal projection to e⊙V and i its actual
inclusion; evaluation preservation is proved from the original Hilbert tensor pairing.
Source: `prop:supported-rank`, mixed normal quotient, without assuming G preserves Z. -/
theorem supportedRadicalNormalResidual_fderiv_projection_factor
    (a : U ≃L[ℝ] (K →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1)
    (Q : K →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) (e : U ≃L[ℝ] U)
    (hA : supportedKernelRightBlock (supportedRadicalRows a r Q) = (e : U →L[ℝ] U))
    (hC : supportedKernelLeftBlock (supportedRadicalRows a r Q) = 0)
    (J : H →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)))
    (i : Z →L[ℝ] H) (P : H →L[ℝ] Z)
    (hP : ∀ v : H, J (i (P v)) (1, 0) = J v (1, 0)) (Y : K →L[ℝ] H) :
    fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q (J.comp Y) =
      fderiv ℝ (supportedRadicalNormalResidual a r w hw) Q
        ((J.comp i).comp (P.comp Y)) := by
  apply supportedRadicalNormalResidual_fderiv_evaluation_congr a r w hw Q e hA hC
  intro k
  exact (hP (Y k)).symm

end GlobalEmbedding.Paper
