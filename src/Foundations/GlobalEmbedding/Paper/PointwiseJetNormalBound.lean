import GlobalEmbedding.Paper.FrameProjectionGap
import GlobalEmbedding.Paper.LinearMapLowerBoundPerturbation
import GlobalEmbedding.Paper.ProjectedMapPerturbation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, uniform quantitative second-jet comparison. -/

namespace GlobalEmbedding.Paper

/-- An elliptic first jet retains one-quarter Gram ellipticity and an explicit normal
second-jet perturbation bound with D₀=3/√lam.

Proof: convert the Gram lower bound to a √lam operator lower bound. The small first-jet
error leaves the lower bound √lam/2. Square to recover the quarter Gram estimate.
The two coercive-frame projection-gap bounds give projection distance at most
(3/√lam) times the first-jet distance. Combine with the projected-map perturbation
identity and the bound M on the old second jet.
Source: `prop:initialization`, quantitative second-jet and phase-margin comparison. -/
theorem pointwise_projected_jet_estimate
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A B : E →L[ℝ] F) (Q Q' : G →L[ℝ] F) (lam M : ℝ) (hlam : 0 < lam)
    (hA : ∀ v, lam * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2)
    (herr : ‖A - B‖ ≤ Real.sqrt lam / 2) (hQ : ‖Q‖ ≤ M) :
    (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖B v‖ ^ 2) ∧
    ‖(LinearMap.range B.toLinearMap)ᗮ.starProjection.comp Q' -
        (LinearMap.range A.toLinearMap)ᗮ.starProjection.comp Q‖ ≤
      ‖Q' - Q‖ + (3 / Real.sqrt lam) * M * ‖A - B‖ := by
  let a := Real.sqrt lam
  have ha : 0 < a := Real.sqrt_pos.mpr hlam
  have hsq : a ^ 2 = lam := Real.sq_sqrt hlam.le
  have hAlow : ∀ v, a * ‖v‖ ≤ ‖A v‖ := by
    intro v
    have hs : (a * ‖v‖) ^ 2 ≤ ‖A v‖ ^ 2 := by
      rw [mul_pow, hsq]
      exact hA v
    exact (sq_le_sq₀ (mul_nonneg ha.le (norm_nonneg v)) (norm_nonneg (A v))).mp hs
  have hBlow : ∀ v, (a / 2) * ‖v‖ ≤ ‖B v‖ := by
    intro v
    have hb := linear_map_lower_bound_perturbation A B a (a / 2) hAlow herr v
    nlinarith
  have hgap0 := frame_normal_projection_gap A B a (a / 2) ha (by positivity) hAlow hBlow
  have hc : ‖A - B‖ * (1 / a + 1 / (a / 2)) = (3 / a) * ‖A - B‖ := by
    field_simp
    ring
  have hgap : ‖(LinearMap.range B.toLinearMap)ᗮ.starProjection -
      (LinearMap.range A.toLinearMap)ᗮ.starProjection‖ ≤ (3 / a) * ‖A - B‖ := by
    simpa only [hc] using hgap0
  refine ⟨?_, ?_⟩
  · intro v
    have hb := (sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg v))
      (norm_nonneg (B v))).mpr (hBlow v)
    calc
      (lam / 4) * ‖v‖ ^ 2 = ((a / 2) * ‖v‖) ^ 2 := by
        rw [mul_pow, div_pow, hsq]
        norm_num
      _ ≤ _ := hb
  · have hm := projected_map_perturbation
      (LinearMap.range A.toLinearMap)ᗮ (LinearMap.range B.toLinearMap)ᗮ Q Q'
    have hterm := mul_le_mul hgap hQ (norm_nonneg Q)
      (mul_nonneg (by positivity : 0 ≤ 3 / a) (norm_nonneg (A - B)))
    nlinarith

end GlobalEmbedding.Paper
