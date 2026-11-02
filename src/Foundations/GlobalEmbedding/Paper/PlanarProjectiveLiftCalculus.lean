import GlobalEmbedding.Paper.PlanarProjectiveHopfGenerator
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.PlanarProjectorSymbol

/-!
# Actual projective observable and scalar-lift derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–260.
DAG node: `planar-projective-lift-calculus`.
The initial selector and its existence remain W6's construction. This file computes
only the actual derivatives of arbitrary genuine smooth observables on the actual RP.
-/
noncomputable section
open Manifold
open scoped ContDiff RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- A genuine smooth projective observable differentiated along the genuine sphere
orbit has precisely its native derivative on the actual descended Hopf generator. -/
theorem planarProjectiveObservable_hasDerivAt {C : ℕ} [Fact (0 < C)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : PlanarRealProjective C → F)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, F) ∞ f) (z : PlanarHopfSphere C) :
    HasDerivAt (fun t : ℝ ↦ f (planarAntipodalProjection (planarHopfFlow t z)))
      (mvfderiv (planarHopfModel C) f (planarAntipodalProjection z)
        (planarProjectiveHopfGenerator (planarAntipodalProjection z))) 0 := by
  rw [planarProjectiveHopfGenerator_mvfderiv f hf]
  have h := hasDerivAt_orbit planarProjectiveHopfFlow (planarProjectiveHopfFlow_contMDiff C)
    planarProjectiveHopfFlow_add f hf 0 (planarAntipodalProjection z)
  simpa only [planarProjectiveHopfFlow_projection, planarHopfFlow_zero] using h

/-- The real scalar lift has its genuine product-rule derivative. All vectors are
in the actual underlying real inner-product space of the original complex ambient. -/
theorem planarProjectivePairing_hasDerivAt {C : ℕ} [Fact (0 < C)]
    (w : PlanarRealProjective C → PlanarHopfAmbient C)
    (hw : ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarHopfAmbient C) ∞ w)
    (z : PlanarHopfSphere C) :
    HasDerivAt (fun t : ℝ ↦
      ⟪w (planarAntipodalProjection (planarHopfFlow t z)),
        (planarHopfFlow t z : PlanarHopfAmbient C)⟫)
      (⟪w (planarAntipodalProjection z),
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫ +
        ⟪mvfderiv (planarHopfModel C) w (planarAntipodalProjection z)
          (planarProjectiveHopfGenerator (planarAntipodalProjection z)),
          (z : PlanarHopfAmbient C)⟫) 0 := by
  have h := (planarProjectiveObservable_hasDerivAt w hw z).inner ℝ (planarHopfOrbit_hasDerivAt z)
  simpa only [planarHopfFlow_zero] using h

/-- The actual projector relation inequality implies a nonzero literal scalar lift
velocity pair, by the already proved true projector derivative and its tangency. -/
theorem planarProjectiveLift_velocityPair_ne_zero {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (a : ℝ) (u w : PlanarHopfAmbient C)
    (h : (a, planarProjectiveProjector (planarAntipodalProjection z) u +
      planarProjectiveProjector (planarAntipodalProjection z)
        (mvfderiv (planarHopfModel C) planarProjectiveProjector
          (planarAntipodalProjection z)
          (planarProjectiveHopfGenerator (planarAntipodalProjection z)) w)) ≠ 0) :
    (a, ⟪w, ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫ +
      ⟪u, (z : PlanarHopfAmbient C)⟫) ≠ (0 : ℝ × ℝ) := by
  have hn := planarProjector_lift_nonzero (z : PlanarHopfAmbient C)
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) w u a
    (mem_sphere_zero_iff_norm.mp z.property) (planarHopfVelocity_orthogonal z)
    (planarProjectiveProjector (planarAntipodalProjection z))
    (mvfderiv (planarHopfModel C) planarProjectiveProjector (planarAntipodalProjection z)
      (planarProjectiveHopfGenerator (planarAntipodalProjection z)))
    (fun _ ↦ rfl) (planarProjectiveProjector_mvfderiv_apply z) h
  simpa only [real_inner_comm (z : PlanarHopfAmbient C) u, add_comm] using hn

/-- The literal two-coordinate planar lift formula has the true orbit derivative.
This does not define a competing selector: W6 can instantiate its own lift definition. -/
theorem planarProjectivePlanarFormula_hasDerivAt {C : ℕ} [Fact (0 < C)]
    (a : PlanarRealProjective C → ℝ)
    (ha : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a)
    (w : PlanarRealProjective C → PlanarHopfAmbient C)
    (hw : ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarHopfAmbient C) ∞ w)
    (z : PlanarHopfSphere C) :
    HasDerivAt (fun t : ℝ ↦
      (a (planarAntipodalProjection (planarHopfFlow t z)) • EuclideanSpace.single 0 1 +
        ⟪w (planarAntipodalProjection (planarHopfFlow t z)),
          (planarHopfFlow t z : PlanarHopfAmbient C)⟫ • EuclideanSpace.single 1 1 : Planar))
      (mvfderiv (planarHopfModel C) a (planarAntipodalProjection z)
          (planarProjectiveHopfGenerator (planarAntipodalProjection z)) • EuclideanSpace.single 0 1 +
        (⟪w (planarAntipodalProjection z),
            ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫ +
          ⟪mvfderiv (planarHopfModel C) w (planarAntipodalProjection z)
            (planarProjectiveHopfGenerator (planarAntipodalProjection z)),
            (z : PlanarHopfAmbient C)⟫) • EuclideanSpace.single 1 1) 0 := by
  exact ((planarProjectiveObservable_hasDerivAt a ha z).smul_const
    (EuclideanSpace.single 0 1 : Planar)).add
      ((planarProjectivePairing_hasDerivAt w hw z).smul_const
        (EuclideanSpace.single 1 1 : Planar))

/-- The genuine ambient projector jet inequality forces the actual two-coordinate
planar velocity vector to be nonzero. No derivative or tangency identity is assumed. -/
theorem planarProjectiveLift_velocity_ne_zero {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (a : ℝ) (u w : PlanarHopfAmbient C)
    (h : (a, planarProjectiveProjector (planarAntipodalProjection z) u +
      planarProjectiveProjector (planarAntipodalProjection z)
        (mvfderiv (planarHopfModel C) planarProjectiveProjector
          (planarAntipodalProjection z)
          (planarProjectiveHopfGenerator (planarAntipodalProjection z)) w)) ≠ 0) :
    (a • EuclideanSpace.single 0 1 +
      (⟪w, ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫ +
        ⟪u, (z : PlanarHopfAmbient C)⟫) • EuclideanSpace.single 1 1 : Planar) ≠ 0 := by
  intro hzero
  have ha := congrArg (fun v : Planar ↦ v 0) hzero
  have hb := congrArg (fun v : Planar ↦ v 1) hzero
  apply planarProjectiveLift_velocityPair_ne_zero z a u w h
  apply Prod.ext
  · simpa using ha
  · simpa using hb

end GlobalEmbedding.Paper
