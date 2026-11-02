import GlobalEmbedding.Paper.PeriodicFlatTorusChartedSpace
import GlobalEmbedding.Paper.PeriodicFlatTorusChartTransition
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Genuine smooth and analytic manifold compatibility of the original flat torus atlas

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-manifold`.
-/

open Set WithLp
open scoped Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual quotient-inverse atlas makes the original flat torus a genuine C^n manifold.

Every chart is an actual local inverse of the original quotient, whose inverse function is
that quotient on the original Euclidean space. The proved actual transition theorem gives
C^n on the full overlap of every two charts. The native Mathlib atlas compatibility theorem
then supplies IsManifold for every n, including true C∞ and the analytic index. This uses
only the explicit original atlas and topology, with no global instance installation.
Source: actual local torus smooth coordinates in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_isManifold (a : ℕ) (n : ℕ∞ω) :
    let _charted := periodicFlatTorusChartedSpace a
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := by
  let _charted := periodicFlatTorusChartedSpace a
  let hf := periodic_flat_torus_local_homeomorph (a := a)
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range hf.localInverseAt at he
  change e' ∈ Set.range hf.localInverseAt at he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  have ht := periodic_flat_torus_chart_transition_contDiff n
    (hf.localInverseAt q) (hf.localInverseAt q')
    (hf.localInverseAt_symm q) (hf.localInverseAt_symm q')
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using ht

#print axioms periodic_flat_torus_isManifold

end GlobalEmbedding.Paper
