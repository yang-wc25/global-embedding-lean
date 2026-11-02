import GlobalEmbedding.Paper.PeriodicFlatTorusManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The original flat-torus quotient projection is genuinely manifold-smooth

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-projection-smooth`.
-/

open Set WithLp IsManifold
open scoped Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual quotient projection is a native C^n map for the actual proved flat-torus atlas.

At each actual Euclidean point its genuine quotient local inverse is an actual atlas member.
The chart inverse is the original quotient projection on all inputs and is manifold-smooth
on its open target through that point. Hence the actual projection is C^n at every point.
All orders, including true C∞ and analyticity, and dimension zero are retained.
Source: actual local torus smooth parameters in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_projection_contMDiff (a : ℕ) (n : ℕ∞ω) :
    let _charted := periodicFlatTorusChartedSpace a
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (fun x : EuclideanSpace ℝ (Fin a) ↦
        toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))) := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  have := periodic_flat_torus_isManifold a n
  intro x
  let hf := periodic_flat_torus_local_homeomorph (a := a)
  have he : hf.localInverseAt x ∈ atlas (EuclideanSpace ℝ (Fin a))
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := mem_range_self x
  have hs := contMDiffAt_symm_of_mem_maximalAtlas (n := n) (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
    (subset_maximalAtlas he) (hf.self_mem_localInverseAt_target (x := x))
  simpa only [hf.localInverseAt_symm x] using hs

#print axioms periodic_flat_torus_projection_contMDiff

end GlobalEmbedding.Paper
