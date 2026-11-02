import GlobalEmbedding.Paper.MatrixFlatCutoffSmoothPullback
import GlobalEmbedding.Paper.ManifoldFlatOnLocalPullbacks
import GlobalEmbedding.Paper.ManifoldFlatOnSMul

/-!
# Actual native manifold flatness of the curvature cutoff and its smooth multiples

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines299–323.
DAG node: `matrix-manifold-flat-curvature-cutoff`.
-/

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual curvature cutoff is flat on its actual curvature-zero set in the
native maximal-atlas flatness predicate.

Proof: actual smoothness is composition of actual scalar cutoff smoothness with
actual κ. Reuse the actual cutoff jets after every actual smooth local pullback;
the root-published native local-pullback criterion gives actual ManifoldFlatOn.
Source: `prop:matrix`, lines299–300. -/
theorem manifold_flat_curvature_cutoff
    {N Q : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]
    (κ : Q → ℝ) (hκ : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ κ) :
    ManifoldFlatOn (I := 𝓘(ℝ, N))
      (fun q ↦ expNegInvGlue (κ q ^ 2)) {q | κ q = 0} := by
  have hs := flat_curvature_cutoff_jets (fun u : ℝ ↦ u) contDiff_id
  apply manifold_flat_on_of_local_pullbacks _ _ (hs.1.contMDiff.comp hκ)
  intro g p hg hp n
  exact flat_cutoff_smooth_pullback κ hκ g p hg hp n

/-- Every actual smooth multiple of the actual curvature cutoff is natively flat
on the actual curvature-zero set.

Proof: reuse the actual native cutoff flatness and root-published actual native
flatness preservation under scalar multiplication; no new chart Leibniz proof.
Source: `prop:matrix`, flatness of angle corrections, lines311–323. -/
theorem manifold_flat_curvature_cutoff_smul
    {N Q E : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Q → ℝ) (hκ : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ κ)
    (g : Q → E) (hg : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ g) :
    ManifoldFlatOn (I := 𝓘(ℝ, N))
      (fun q ↦ expNegInvGlue (κ q ^ 2) • g q) {q | κ q = 0} :=
  manifold_flat_on_smul (manifold_flat_curvature_cutoff κ hκ) g hg

#print axioms manifold_flat_curvature_cutoff
#print axioms manifold_flat_curvature_cutoff_smul

end GlobalEmbedding.Paper
