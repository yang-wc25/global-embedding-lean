import GlobalEmbedding.Paper.PlanarProjectiveMapLift
import GlobalEmbedding.Paper.PlanarProjectiveLiftCalculus

/-!
# Actual derivative and nonvanishing of the canonical projective map lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–260.
DAG node: `planar-projective-map-lift-derivative`.
The actual lift and relation are the canonical W6 definitions. This file only proves
the assigned derivative/nonvanishing bridge; the formal solver and existence remain W6.
-/
noncomputable section
open Manifold
open scoped ContDiff RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- The canonical actual projective map lift has its true sphere Hopf-orbit derivative.
The observable derivative is the genuine shared projective orbit derivative. -/
theorem planarProjectiveMapLift_hasDerivAt {C : ℕ} [Fact (0 < C)]
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C)
    (hF : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) ∞ F)
    (z : PlanarHopfSphere C) :
    HasDerivAt (fun t : ℝ ↦ planarProjectiveMapLift F (planarHopfFlow t z))
      ((orbitDeriv planarProjectiveHopfFlow F (planarAntipodalProjection z)).1 •
          EuclideanSpace.single 0 1 +
        (⟪(orbitDeriv planarProjectiveHopfFlow F (planarAntipodalProjection z)).2,
            (z : PlanarHopfAmbient C)⟫ +
          ⟪(F (planarAntipodalProjection z)).2,
            ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫) •
          EuclideanSpace.single 1 1) 0 := by
  have hd := planarProjectiveObservable_hasDerivAt F hF z
  rw [planarProjectiveHopfGenerator_mvfderiv F hF] at hd
  have ha : HasDerivAt
      (fun t : ℝ ↦ (F (planarAntipodalProjection (planarHopfFlow t z))).1)
      (orbitDeriv planarProjectiveHopfFlow F (planarAntipodalProjection z)).1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ (PlanarHopfAmbient C)).hasFDerivAt.comp_hasDerivAt 0 hd
  have hw : HasDerivAt
      (fun t : ℝ ↦ (F (planarAntipodalProjection (planarHopfFlow t z))).2)
      (orbitDeriv planarProjectiveHopfFlow F (planarAntipodalProjection z)).2 0 :=
    (ContinuousLinearMap.snd ℝ ℝ (PlanarHopfAmbient C)).hasFDerivAt.comp_hasDerivAt 0 hd
  have hi := hw.inner ℝ (planarHopfOrbit_hasDerivAt z)
  have hv := (ha.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    (hi.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  convert hv using 1 <;> simp only [planarProjectiveMapLift, planarHopfFlow_zero, add_comm]
  rfl

/-- A true holonomic solution of the actual projective projector relation has
nowhere-zero genuine Hopf derivative after the canonical lift. -/
theorem planarProjectiveMapLift_deriv_ne_zero {C : ℕ} [Fact (0 < C)]
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C)
    (hF : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) ∞ F)
    (hsol : ∀ x, oneJetExt (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) F x ∈
      planarInitialProjectiveRelation C) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (planarProjectiveMapLift F) z ≠ 0 := by
  let x := planarAntipodalProjection z
  let u := orbitDeriv planarProjectiveHopfFlow F x
  have h := hsol x
  change ((mvfderiv (planarHopfModel C) F x (planarProjectiveHopfGenerator x)).1,
    planarProjectiveProjector x
        (mvfderiv (planarHopfModel C) F x (planarProjectiveHopfGenerator x)).2 +
      planarProjectiveProjector x (planarInitialProjectorDerivative x (F x).2)) ≠ 0 at h
  rw [planarProjectiveHopfGenerator_mvfderiv F hF] at h
  have hq : planarInitialProjectorDerivative x =
      mvfderiv (planarHopfModel C) planarProjectiveProjector x
        (planarProjectiveHopfGenerator x) :=
    (planarProjectiveHopfGenerator_mvfderiv planarProjectiveProjector
      (planarProjectiveProjector_contMDiff C) x).symm
  rw [hq] at h
  have hn := planarProjectiveLift_velocity_ne_zero z u.1 u.2 (F x).2 h
  have he := (planarProjectiveMapLift_hasDerivAt F hF z).deriv
  change orbitDeriv planarHopfFlow (planarProjectiveMapLift F) z =
    u.1 • EuclideanSpace.single 0 1 +
      (⟪u.2, (z : PlanarHopfAmbient C)⟫ +
        ⟪(F x).2, ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫) •
        EuclideanSpace.single 1 1 at he
  rw [he]
  simpa only [add_comm] using hn

end GlobalEmbedding.Paper
