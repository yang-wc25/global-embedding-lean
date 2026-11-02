import GlobalEmbedding.Paper.PlanarHopfFlow
import GlobalEmbedding.Paper.PlanarNativeCurvature
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth

/-!
# The actual Hopf curvature component of the original planar selector

Source: `main.tex`, `lem:planar`, lines 252–265.
DAG: `planar-hopf-curvature`.
Every input is a property of the actually constructed original planar map.
The actual Hopf geometry and all actual derivative regularity are proved
prerequisites, and the curvature is genuinely constructed from that same map.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- On the genuine Hopf sphere, actual native smoothness, unit speed and the
original antipodal reflection imply the whole original curvature conclusion.
The curvature is additionally antipodal odd. In particular no circle-angle
lift, formal derivative, desired curvature sign or derivative-regularity
assumption is supplied. The original C≥2 gives the positive-C instance. -/
theorem planar_hopf_curvature {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hreflect : ∀ z, f (-z) = planarReflection (f z)) :
    ∃ κ : PlanarHopfSphere C → ℝ,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ ∧
      (∀ z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z =
        κ z • planarQuarterTurn (orbitDeriv planarHopfFlow f z)) ∧
      (∀ z, ∃ t s : ℝ, κ (planarHopfFlow t z) < 0 ∧
        0 < κ (planarHopfFlow s z)) ∧
      (∀ z, κ (-z) = -κ z) := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C)
    (orbitDeriv planarHopfFlow f) hv
  have hfd (z : PlanarHopfSphere C) :
      Differentiable ℝ (fun t ↦ f (planarHopfFlow t z)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf t z).differentiableAt
  have hvd (z : PlanarHopfSphere C) :
      Differentiable ℝ (fun t ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t z)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add (orbitDeriv planarHopfFlow f) hv t z).differentiableAt
  have hhalf (z : PlanarHopfSphere C) :
      f (planarHopfFlow (1 / 2) z) = planarReflection (f z) := by
    rw [planarHopfFlow_half]
    exact hreflect z
  refine ⟨planarOrbitCurvature planarHopfFlow f,
    planarOrbitCurvature_contMDiff planarHopfFlow f hv ha, ?_, ?_, ?_⟩
  · exact planarOrbitCurvature_acceleration planarHopfFlow planarHopfFlow_add
      planarHopfFlow_zero f hfd hvd hunit
  · intro z
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := planarOrbitCurvature_both_signs planarHopfFlow
      planarHopfFlow_add planarHopfFlow_one f hfd hvd hunit hhalf z
    exact ⟨t, s, ht, hs⟩
  · intro z
    simpa only [planarHopfFlow_half] using
      (planarOrbitCurvature_half_odd planarHopfFlow planarHopfFlow_add
        planarHopfFlow_zero f hfd hvd hhalf z)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planar_hopf_curvature
