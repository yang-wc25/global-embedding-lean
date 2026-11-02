import GlobalEmbedding.Targets.PlanarSelectors

/-!
# The actual planar map used throughout the matrix construction

Source: `main.tex`, `lem:planar` and `prop:matrix`, lines245–296.
DAG: `matrix-planar-selector-properties`.
The predicate concerns one specified actual map; its curvature is the actual native
orbit curvature. It introduces neither a new derivative nor existential geometry.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- All properties of the same actual planar selector used in `prop:matrix`.
The curvature is literally the inner product defining `planarOrbitCurvature`.
Source: `lem:planar`, lines245–265; `prop:matrix`, lines272–296. -/
structure MatrixPlanarSelectorProperties {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) : Prop where
  smooth : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f
  unit_speed : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1
  reflection : ∀ z, f (-z) = planarReflection (f z)
  signed_area : ∀ z, orbitAverage planarHopfFlow
    (fun w ↦ f w 0 * orbitDeriv planarHopfFlow f w 1 -
      f w 1 * orbitDeriv planarHopfFlow f w 0) z = 0
  orbit_analytic : ∀ z,
    AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) Set.univ
  curvature_smooth : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
    (planarOrbitCurvature planarHopfFlow f)
  acceleration : ∀ z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z =
    planarOrbitCurvature planarHopfFlow f z • planarQuarterTurn (orbitDeriv planarHopfFlow f z)
  curvature_signs : ∀ z, ∃ t s : ℝ,
    planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) < 0 ∧
      0 < planarOrbitCurvature planarHopfFlow f (planarHopfFlow s z)

/-- The already proved original selector supplies this fixed-map predicate with
its actual canonical curvature.

Proof: take the original selector and its curvature. The unit-speed identity and
its acceleration equation identify that curvature with the actual determinant
of velocity and acceleration. Substitute this equality in all original clauses.
Source: `lem:planar`, lines245–265. -/
theorem matrix_planar_selector_exists (C : ℕ) (hC : 2 ≤ C) :
    letI : Fact (0 < C) := ⟨by omega⟩
    ∃ f : PlanarHopfSphere C → Planar, MatrixPlanarSelectorProperties f := by
  let _ : Fact (0 < C) := ⟨by omega⟩
  obtain ⟨f, κ, hf, hu, hr, harea, hana, hκ, ha, hsign⟩ := planar_hopf_selector C hC
  have he : planarOrbitCurvature planarHopfFlow f = κ := by
    funext z
    have hn := congrArg (fun r : ℝ ↦ r ^ 2) (hu z)
    have hn' : orbitDeriv planarHopfFlow f z 0 ^ 2 +
        orbitDeriv planarHopfFlow f z 1 ^ 2 = 1 := by
      simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using hn
    rw [planarOrbitCurvature_coordinates, ha z]
    change orbitDeriv planarHopfFlow f z 0 * (κ z * orbitDeriv planarHopfFlow f z 0) -
      orbitDeriv planarHopfFlow f z 1 * (κ z * -orbitDeriv planarHopfFlow f z 1) = κ z
    calc
      _ = κ z * (orbitDeriv planarHopfFlow f z 0 ^ 2 +
        orbitDeriv planarHopfFlow f z 1 ^ 2) := by ring
      _ = κ z := by rw [hn', mul_one]
  refine ⟨f, hf, hu, hr, harea, hana, ?_, ?_, ?_⟩
  · simpa only [he] using hκ
  · simpa only [he] using ha
  · simpa only [he] using hsign

#print axioms matrix_planar_selector_exists

end GlobalEmbedding.Paper
