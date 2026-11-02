import GlobalEmbedding.Paper.CollarCKAnalyticTaylorPackaging

/-!
# Actual analytic germs are determined by the shared commutative coefficients

Source: Gantumur, notes2, Theorem 18, uniqueness from the formal Taylor solution.
The multilinear witnesses may be nonsymmetric. Their diagonal terms are determined by the
accepted commutative coefficient formula, which suffices for native uniqueness of actual sums.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Paper

variable {σ F : Type*} [Fintype σ] [DecidableEq σ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equal shared coefficients of genuine expansions give equal actual analytic germs.
Source: Gantumur, Theorem 18. The accepted homogeneous coefficient formula gives equality of
every diagonal term. Both genuine expansions supply actual sums on a common neighborhood;
uniqueness of those sums gives equality there. No equality of nonsymmetric witnesses is used. -/
theorem collarCKAnalyticGerm_of_coefficients
    (f g : (σ → ℝ) → F) (p q : FormalMultilinearSeries ℝ (σ → ℝ) F)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hcoeff : ∀ d, collarCKTaylorCoeff p d = collarCKTaylorCoeff q d) :
    f =ᶠ[𝓝 0] g := by
  have hdiag (k : ℕ) (z : σ → ℝ) : p k (fun _ ↦ z) = q k (fun _ ↦ z) := by
    rw [collarCKTaylorCoeff_homogeneous p k z, collarCKTaylorCoeff_homogeneous q k z]
    simp only [hcoeff]
  filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with z hz hz'
  have hterms : (fun k ↦ p k (fun _ ↦ z - 0)) = (fun k ↦ q k (fun _ ↦ z - 0)) := by
    funext k
    exact hdiag k (z - 0)
  rw [hterms] at hz
  exact hz.unique hz'

/-- The same full coefficients force equality on one genuine positive real ball.
Source: Gantumur, local analytic uniqueness. Convert the actual germ equality above with the
native metric neighborhood basis; no common radius or pointwise choice is assumed. -/
theorem collarCKAnalyticBall_of_coefficients
    (f g : (σ → ℝ) → F) (p q : FormalMultilinearSeries ℝ (σ → ℝ) F)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hcoeff : ∀ d, collarCKTaylorCoeff p d = collarCKTaylorCoeff q d) :
    ∃ δ : ℝ, 0 < δ ∧ Set.EqOn f g (Metric.ball 0 δ) := by
  obtain ⟨δ, hδ, heq⟩ := Metric.eventually_nhds_iff_ball.mp
    (collarCKAnalyticGerm_of_coefficients f g p q hp hq hcoeff)
  exact ⟨δ, hδ, heq⟩

#print axioms collarCKAnalyticGerm_of_coefficients
#print axioms collarCKAnalyticBall_of_coefficients
end GlobalEmbedding.Paper
