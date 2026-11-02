import GlobalEmbedding.Paper.PeriodicFlatTorusLocalHomeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# A genuine Euclidean charted-space structure on the original L2 flat torus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-charted-space`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual original flat torus has Euclidean charts given by local quotient inverses.

Choose an actual lift of each point using the proved surjectivity. The actual local
homeomorphism supplies a local inverse through that lift. These genuine charts cover every
point and preserve the original flat-torus topology. This explicit charted-space data is not
installed as a global instance; smooth compatibility is a separate theorem.
Source: local torus charts in the proof of `lem:balanced`. -/
@[instance_reducible]
noncomputable def periodicFlatTorusChartedSpace (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := by
  let hf := periodic_flat_torus_local_homeomorph (a := a)
  let r := fun q : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
    (periodic_flat_torus_projection.surjective q).choose
  have hr (q : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) :
      toLp 2 (fun i : Fin a ↦ (r q i : AddCircle (1 : ℝ))) = q :=
    (periodic_flat_torus_projection.surjective q).choose_spec
  exact
    { atlas := Set.range hf.localInverseAt
      chartAt := fun q ↦ hf.localInverseAt (r q)
      mem_chart_source := fun q ↦ by
        have hmem := hf.apply_self_mem_localInverseAt_source (x := r q)
        simpa only [hr q] using hmem
      chart_mem_atlas := fun q ↦ mem_range_self (r q) }

#print axioms periodicFlatTorusChartedSpace

end GlobalEmbedding.Paper
