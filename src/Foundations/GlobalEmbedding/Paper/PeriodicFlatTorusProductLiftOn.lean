import GlobalEmbedding.Paper.PeriodicFlatTorusProductLiftAt

/-!
# Genuine open-domain joint parameter/flat-torus smoothness is equivalent to lift smoothness

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-product-lift-on`.
-/

open Set WithLp
open scoped Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Native joint C^n on an open parameter domain times the actual torus is exactly C^n of
its actual full Euclidean lift on that parameter domain times the Euclidean shift space.

Openness upgrades the given within-domain differentiability to pointwise differentiability.
Apply the proved actual product lifting equivalence at every lift. Actual projection
surjectivity supplies a lift for every torus point in the reverse direction. No continuity
of the given function is assumed separately. Source: full joint parameter/fiber regularity
in local principal-torus charts in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_product_lift_contMDiffOn_iff
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {a : ℕ} (n : ℕ∞ω)
    (U : Set P) (hU : IsOpen U)
    (f : P × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) → V) :
    let _charted := periodicFlatTorusChartedSpace a
    ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, V)) n f
        (U ×ˢ univ) ↔
      ContDiffOn ℝ n (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        f (z.1, toLp 2 (fun i : Fin a ↦ (z.2 i : AddCircle (1 : ℝ))))) (U ×ˢ univ) := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  have := periodic_flat_torus_isManifold a n
  constructor
  · intro hf
    apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
    intro z hz
    have hc := hf.contMDiffAt (x := (z.1,
      toLp 2 (fun i : Fin a ↦ (z.2 i : AddCircle (1 : ℝ)))))
      ((hU.prod isOpen_univ).mem_nhds ⟨hz.1, mem_univ _⟩)
    exact (periodic_flat_torus_product_lift_contMDiffAt_iff n f z.1 z.2).mp hc
  · intro hf z hz
    obtain ⟨x, hx⟩ := periodic_flat_torus_projection.surjective z.2
    have hLift := hf.contDiffAt (x := (z.1, x))
      ((hU.prod isOpen_univ).mem_nhds ⟨hz.1, mem_univ _⟩)
    have hc := (periodic_flat_torus_product_lift_contMDiffAt_iff n f z.1 x).mpr hLift
    change toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))) = z.2 at hx
    rw [hx] at hc
    exact hc.contMDiffWithinAt

#print axioms periodic_flat_torus_product_lift_contMDiffOn_iff

end GlobalEmbedding.Paper
