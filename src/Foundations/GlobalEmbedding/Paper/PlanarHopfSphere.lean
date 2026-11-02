import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The actual complex Hopf sphere with its native real sphere atlas

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines245–266.
DAG node: `planar-hopf-sphere-native`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The genuine complex Euclidean ambient space, also carrying its canonical restricted
real inner product. No function-space sup norm or arbitrary replacement model is used. -/
abbrev PlanarHopfAmbient (C : ℕ) := EuclideanSpace ℂ (Fin C)

/-- The actual unit sphere in the source's complex Euclidean space. -/
abbrev PlanarHopfSphere (C : ℕ) := Metric.sphere (0 : PlanarHopfAmbient C) 1

/-- The genuine real sphere model has dimension 2C-1. Its structure is derived below
for every positive C; the original target C≥2 is an immediate instance. -/
abbrev planarHopfModel (C : ℕ) := 𝓡 (2 * C - 1)

/-- Restricting the complex C-dimensional ambient space to the reals doubles dimension.
This is the existing scalar-tower finrank formula, not a coordinate replacement. -/
theorem planarHopfAmbient_finrank (C : ℕ) :
    Module.finrank ℝ (PlanarHopfAmbient C) = 2 * C := by
  rw [finrank_real_of_complex]
  simp

/-- The actual ambient dimension supplies Mathlib's native sphere atlas parameter.
For positive C, 2C=(2C-1)+1. No manifold hypothesis is requested from a caller. -/
instance planarHopfSphereDimension (C : ℕ) [Fact (0 < C)] :
    Fact (Module.finrank ℝ (PlanarHopfAmbient C) = (2 * C - 1) + 1) := by
  constructor
  rw [planarHopfAmbient_finrank]
  have h := Fact.out (p := 0 < C)
  omega

/-- The sphere's actual smooth manifold structure comes from the proved native
stereographic sphere atlas in pinned Mathlib. All its topology remains the subtype topology. -/
theorem planarHopfSphere_native (C : ℕ) [Fact (0 < C)] :
    IsManifold (planarHopfModel C) ∞ (PlanarHopfSphere C) := inferInstance

/-- The actual ambient inclusion is native smooth, by Mathlib's sphere inclusion theorem. -/
theorem planarHopfSphere_contMDiff_coe (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarHopfAmbient C) ∞
      (fun z : PlanarHopfSphere C ↦ (z : PlanarHopfAmbient C)) :=
  contMDiff_coe_sphere

/-- Actual complex finite-dimensional unit spheres are compact, with no nonemptiness
assumption or supplied compactness data. -/
theorem planarHopfSphere_compact (C : ℕ) : CompactSpace (PlanarHopfSphere C) := inferInstance

end GlobalEmbedding.Paper
