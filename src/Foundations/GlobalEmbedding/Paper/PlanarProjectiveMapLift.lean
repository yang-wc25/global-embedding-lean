import GlobalEmbedding.Paper.PlanarProjectorMapRelation
import GlobalEmbedding.Paper.PlanarProjectiveHopfGenerator
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth

/-!
# Actual native projective relation and explicit reflection-equivariant sphere lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
These are genuine geometry and calculus interfaces; no initial map or h-principle solution
is assumed to exist. An input ordinary map is lifted by its explicit source formula.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual derivative of the actual projective projector along the actual projective flow. -/
def planarInitialProjectorDerivative {C : ℕ} :
    PlanarRealProjective C → PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C :=
  orbitDeriv planarProjectiveHopfFlow planarProjectiveProjector

/-- The genuine native projector maps relation on the actual real-projective Hopf base. -/
def planarInitialProjectiveRelation (C : ℕ) [Fact (0 < C)] :
    RelMfld (planarHopfModel C) (PlanarRealProjective C)
      𝓘(ℝ, ℝ × PlanarHopfAmbient C) (ℝ × PlanarHopfAmbient C) :=
  planarProjectorJetRelation (planarProjectiveHopfGeneratorSection C)
    planarProjectiveProjector planarInitialProjectorDerivative

/-- The actual derivative coefficient field is native smooth by the genuine orbit calculus. -/
theorem planarInitialProjectorDerivative_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C) ∞
      (@planarInitialProjectorDerivative C) :=
  contMDiff_orbitDeriv planarProjectiveHopfFlow (planarProjectiveHopfFlow_contMDiff C)
    planarProjectiveProjector (planarProjectiveProjector_contMDiff C)

/-- The actual relation is open without any additional geometric or solver hypothesis. -/
theorem planarInitialProjectiveRelation_isOpen (C : ℕ) [Fact (0 < C)] :
    IsOpen (planarInitialProjectiveRelation C) :=
  isOpen_planarProjectorJetRelation (planarProjectiveHopfGeneratorSection C)
    planarProjectiveProjector planarInitialProjectorDerivative
    (planarProjectiveProjector_contMDiff C) (planarInitialProjectorDerivative_contMDiff C)

/-- The actual relation is ample, using real unit representatives only pointwise. -/
theorem planarInitialProjectiveRelation_ample (C : ℕ) [Fact (0 < C)] :
    (planarInitialProjectiveRelation C).Ample := by
  apply ample_planarProjectorJetRelation
  intro x
  obtain ⟨z, rfl⟩ := planarAntipodalProjection_surjective C x
  refine ⟨(z : PlanarHopfAmbient C), mem_sphere_zero_iff_norm.mp z.property, ?_⟩
  intro w
  rfl

/-- Lift an actual ordinary map on the actual projective base to a reflection-equivariant
planar map on the whole actual sphere. This is a formula, not a chosen hypothetical section. -/
def planarProjectiveMapLift {C : ℕ}
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C) (z : PlanarHopfSphere C) : Planar :=
  (F (planarAntipodalProjection z)).1 • EuclideanSpace.single 0 1 +
    ⟪(F (planarAntipodalProjection z)).2, (z : PlanarHopfAmbient C)⟫ •
      EuclideanSpace.single 1 1

/-- The first coordinate is the genuine invariant scalar map. -/
@[simp] theorem planarProjectiveMapLift_zero {C : ℕ}
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C) (z : PlanarHopfSphere C) :
    planarProjectiveMapLift F z 0 = (F (planarAntipodalProjection z)).1 := by
  simp [planarProjectiveMapLift]

/-- The second coordinate is the genuine odd scalar pairing with the sphere representative. -/
@[simp] theorem planarProjectiveMapLift_one {C : ℕ}
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C) (z : PlanarHopfSphere C) :
    planarProjectiveMapLift F z 1 =
      ⟪(F (planarAntipodalProjection z)).2, (z : PlanarHopfAmbient C)⟫ := by
  simp [planarProjectiveMapLift]

/-- Native smoothness of the explicit lift follows from the actual smooth projection and
the actual continuous bilinear real inner product. -/
theorem planarProjectiveMapLift_contMDiff {C : ℕ} [Fact (0 < C)]
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C)
    (hF : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ × PlanarHopfAmbient C) ∞ F) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ (planarProjectiveMapLift F) := by
  have hf := hF.comp (planarAntipodalProjection_contMDiff C)
  have ha := (ContinuousLinearMap.fst ℝ ℝ (PlanarHopfAmbient C)).contDiff.contMDiff.comp hf
  have hw := (ContinuousLinearMap.snd ℝ ℝ (PlanarHopfAmbient C)).contDiff.contMDiff.comp hf
  have hb := ((innerSL ℝ).contDiff.contMDiff.comp hw).clm_apply
    (planarHopfSphere_contMDiff_coe C)
  exact (ha.smul contMDiff_const).add (hb.smul contMDiff_const)

/-- The explicit lift has the original antipodal reflection law on the entire sphere. -/
theorem planarProjectiveMapLift_reflection {C : ℕ}
    (F : PlanarRealProjective C → ℝ × PlanarHopfAmbient C) (z : PlanarHopfSphere C) :
    planarProjectiveMapLift F (-z) = planarReflection (planarProjectiveMapLift F z) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [planarReflection]

/-- The actual coefficient Q has precisely the genuine lifted rank-one derivative formula. -/
theorem planarInitialProjectorDerivative_projection_apply {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (w : PlanarHopfAmbient C) :
    planarInitialProjectorDerivative (planarAntipodalProjection z) w =
      ⟪(z : PlanarHopfAmbient C), w⟫ •
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) +
        ⟪((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)), w⟫ •
          (z : PlanarHopfAmbient C) := by
  change orbitDeriv planarProjectiveHopfFlow planarProjectiveProjector
    (planarAntipodalProjection z) w = _
  rw [← planarProjectiveHopfGenerator_mvfderiv planarProjectiveProjector
    (planarProjectiveProjector_contMDiff C)]
  exact planarProjectiveProjector_mvfderiv_apply z w

#print axioms planarInitialProjectorDerivative_contMDiff
#print axioms planarInitialProjectiveRelation_isOpen
#print axioms planarInitialProjectiveRelation_ample
#print axioms planarProjectiveMapLift_zero
#print axioms planarProjectiveMapLift_one
#print axioms planarProjectiveMapLift_contMDiff
#print axioms planarProjectiveMapLift_reflection
#print axioms planarInitialProjectorDerivative_projection_apply

end GlobalEmbedding.Paper
