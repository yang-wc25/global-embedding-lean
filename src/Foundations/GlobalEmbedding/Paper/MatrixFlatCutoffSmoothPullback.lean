import GlobalEmbedding.Paper.MatrixFlatCurvatureCutoffJets
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Full flat cutoff jets in arbitrary smooth local parameterizations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines 299–300.
DAG node: `matrix-flat-cutoff-smooth-pullback`.
-/

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual cutoff has zero full jets at every zero of curvature after any actual
smooth local parameterization into its native manifold.

Proof: reuse the accepted scalar full-jet theorem for the actual scalar function
u ↦ expNegInvGlue(u²) at0. Native smooth composition makes κ∘g genuinely ContDiffAt.
In the native full Frechet composition formula every term contains a scalar outer
jet, all of which vanish at0. This applies in particular to every smooth local chart
inverse; no chosen chart-flatness predicate is assumed.
Source: `prop:matrix`, lines 299–300. -/
theorem flat_cutoff_smooth_pullback
    {P N Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q]
    (κ : Q → ℝ) (hκ : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ κ)
    (g : P → Q) (p : P) (hg : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, N) ∞ g p)
    (hzero : κ (g p) = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ expNegInvGlue (κ (g x) ^ 2)) p = 0 := by
  have hs := flat_curvature_cutoff_jets (fun u : ℝ ↦ u) contDiff_id
  have hinner : ContDiffAt ℝ ∞ (fun x ↦ κ (g x)) p :=
    (hκ.contMDiffAt.comp p hg).contDiffAt
  change iteratedFDeriv ℝ n
    ((fun u : ℝ ↦ expNegInvGlue (u ^ 2)) ∘ (fun x ↦ κ (g x))) p = 0
  rw [iteratedFDeriv_comp hs.1.contDiffAt hinner
    (show (n : ℕ∞ω) ≤ ∞ by simp)]
  ext v
  simp only [hzero, FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries,
    hs.2.2 0 rfl, zero_apply, Finset.sum_const_zero]

/-- Odd curvature makes its actual cutoff invariant under the symmetry.
Source: `prop:matrix`, lines 299–300; the sign disappears after squaring. -/
theorem flat_cutoff_invariant_of_odd
    {Q : Type*} (κ : Q → ℝ) (τ : Q → Q) (hodd : ∀ q, κ (τ q) = -κ q) (q : Q) :
    expNegInvGlue (κ (τ q) ^ 2) = expNegInvGlue (κ q ^ 2) := by
  rw [hodd, neg_sq]

#print axioms flat_cutoff_smooth_pullback
#print axioms flat_cutoff_invariant_of_odd

end GlobalEmbedding.Paper
