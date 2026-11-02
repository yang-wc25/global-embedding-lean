import GlobalEmbedding.Paper.PlanarAntipodalSmoothAtlas
import GlobalEmbedding.Paper.PlanarHopfGenerator
import Mathlib.Analysis.InnerProductSpace.Calculus
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness

/-!
# The actual real rank-one projector on the antipodal quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-real-rank-one-projector`.
-/
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- The real orthogonal projector onto the line through an actual sphere point.
The underlying real inner product is essential; this is not a complex-line projector. -/
def planarSphereProjector {C : ℕ} (z : PlanarHopfSphere C) :
    PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C :=
  InnerProductSpace.rankOne ℝ (z : PlanarHopfAmbient C) (z : PlanarHopfAmbient C)

@[simp] theorem planarSphereProjector_apply {C : ℕ} (z : PlanarHopfSphere C)
    (w : PlanarHopfAmbient C) :
    planarSphereProjector z w = ⟪(z : PlanarHopfAmbient C), w⟫ • (z : PlanarHopfAmbient C) := rfl

/-- The two sign changes cancel, so the actual projector is antipodal invariant. -/
@[simp] theorem planarSphereProjector_neg {C : ℕ} (z : PlanarHopfSphere C) :
    planarSphereProjector (-z) = planarSphereProjector z := by
  ext w
  simp

/-- The endomorphism-valued projector is native smooth, by the actual continuous
bilinear rank-one operator applied twice to the native smooth sphere inclusion. -/
theorem planarSphereProjector_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C) ∞
      (@planarSphereProjector C) := by
  intro z
  apply (manifold_finite_operator_smooth_iff (@planarSphereProjector C) z).mpr
  intro w
  change ContMDiffAt (planarHopfModel C) 𝓘(ℝ, PlanarHopfAmbient C) ∞
    (fun y : PlanarHopfSphere C ↦ ⟪(y : PlanarHopfAmbient C), w⟫ • (y : PlanarHopfAmbient C)) z
  have hi : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun y : PlanarHopfSphere C ↦ ⟪(y : PlanarHopfAmbient C), w⟫) := by
    have hh := (innerSL ℝ w).contDiff.contMDiff.comp (planarHopfSphere_contMDiff_coe C)
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm w] using hh
  exact (hi.smul (planarHopfSphere_contMDiff_coe C)).contMDiffAt

/-- The projector on actual real projective space is defined by quotient recursion,
using the proved antipodal invariance. -/
def planarProjectiveProjector {C : ℕ} (x : PlanarRealProjective C) :
    PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C :=
  Quotient.lift planarSphereProjector (fun z w h ↦ by
    rcases (planarAntipodalProjection_eq_iff z w).mp (Quotient.sound h) with hzw | hzw
    · rw [hzw]
    · rw [hzw, planarSphereProjector_neg]) x

/-- Actual pullback of the descended projector is exactly the sphere projector. -/
@[simp] theorem planarProjectiveProjector_projection {C : ℕ} (z : PlanarHopfSphere C) :
    planarProjectiveProjector (planarAntipodalProjection z) = planarSphereProjector z := rfl

/-- Native smoothness descends through the genuine proved smooth double covering. -/
theorem planarProjectiveProjector_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C) ∞
      (@planarProjectiveProjector C) :=
  (planarAntipodal_contMDiff_iff_pullback _ planarProjectiveProjector).mpr
    (planarSphereProjector_contMDiff C)

/-- Unit norm makes the real rank-one projector idempotent. -/
theorem planarSphereProjector_idempotent {C : ℕ} (z : PlanarHopfSphere C) :
    IsIdempotentElem (planarSphereProjector z) :=
  InnerProductSpace.isIdempotentElem_rankOne_self (mem_sphere_zero_iff_norm.mp z.property)

/-- The real line representative is fixed by its orthogonal projector. -/
@[simp] theorem planarSphereProjector_self {C : ℕ} (z : PlanarHopfSphere C) :
    planarSphereProjector z (z : PlanarHopfAmbient C) = (z : PlanarHopfAmbient C) := by
  simp [mem_sphere_zero_iff_norm.mp z.property]

/-- The actual range is exactly the real line, with no complex-rank substitution. -/
theorem planarSphereProjector_range {C : ℕ} (z : PlanarHopfSphere C) :
    (planarSphereProjector z).toLinearMap.range = ℝ ∙ (z : PlanarHopfAmbient C) := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨⟪(z : PlanarHopfAmbient C), u⟫, rfl⟩
  · intro hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨a • (z : PlanarHopfAmbient C), by simp⟩

/-- Every actual projector has real rank one. -/
theorem planarSphereProjector_finrank {C : ℕ} (z : PlanarHopfSphere C) :
    Module.finrank ℝ (planarSphereProjector z).toLinearMap.range = 1 := by
  rw [planarSphereProjector_range]
  apply finrank_span_singleton
  intro hz
  have hn := mem_sphere_zero_iff_norm.mp z.property
  simp [hz] at hn

/-- The actual Hopf velocity is perpendicular to the sphere radius. This also follows
by differentiating the literal constant unit norm of the actual orbit. -/
theorem planarHopfVelocity_orthogonal {C : ℕ} (z : PlanarHopfSphere C) :
    ⟪(z : PlanarHopfAmbient C),
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))⟫ = 0 := by
  have hd := (planarHopfOrbit_hasDerivAt z).inner ℝ (planarHopfOrbit_hasDerivAt z)
  have he : (fun t : ℝ ↦ ⟪(planarHopfFlow t z : PlanarHopfAmbient C),
      (planarHopfFlow t z : PlanarHopfAmbient C)⟫) = fun _ ↦ (1 : ℝ) := by
    funext t
    simp [mem_sphere_zero_iff_norm.mp (planarHopfFlow t z).property]
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [planarHopfFlow_zero] at hh
  rw [real_inner_comm
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C))] at hh
  rw [real_inner_comm]
  linarith

/-- The true derivative of the literal sphere projector, evaluated on any fixed
ambient vector, along the actual period-one Hopf orbit. -/
theorem planarSphereProjector_hasDerivAt {C : ℕ} (z : PlanarHopfSphere C)
    (w : PlanarHopfAmbient C) :
    HasDerivAt (fun t : ℝ ↦ planarSphereProjector (planarHopfFlow t z) w)
      (⟪(z : PlanarHopfAmbient C), w⟫ •
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) +
        ⟪((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)), w⟫ •
          (z : PlanarHopfAmbient C)) 0 := by
  have hi := (planarHopfOrbit_hasDerivAt z).inner ℝ (hasDerivAt_const (0 : ℝ) w)
  have hh := hi.smul (planarHopfOrbit_hasDerivAt z)
  convert hh using 1
  · rfl
  · simp only [planarHopfFlow_zero, inner_zero_right, zero_add]

/-- The actual native derivative of the operator-valued projector along the genuine
Hopf generator agrees pointwise with the literal orbit derivative just computed. -/
theorem planarSphereProjector_mvfderiv_apply {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (w : PlanarHopfAmbient C) :
    mvfderiv (planarHopfModel C) planarSphereProjector z (planarHopfGenerator z) w =
      ⟪(z : PlanarHopfAmbient C), w⟫ •
          ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) +
        ⟪((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)), w⟫ •
          (z : PlanarHopfAmbient C) := by
  rw [planarHopfGenerator_mvfderiv _ (planarSphereProjector_contMDiff C)]
  have hp : ContDiff ℝ ∞ (fun t : ℝ ↦ planarSphereProjector (planarHopfFlow t z)) :=
    ((planarSphereProjector_contMDiff C).comp ((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const))).contDiff
  change deriv (fun t : ℝ ↦ planarSphereProjector (planarHopfFlow t z)) 0 w = _
  calc
    _ = deriv (fun t : ℝ ↦ planarSphereProjector (planarHopfFlow t z) w) 0 := by
      have he := deriv_clm_apply
        ((hp.differentiable (by simp)).differentiableAt (x := 0))
        (differentiableAt_const (c := w) (x := (0 : ℝ)))
      simpa only [deriv_const, map_zero, add_zero] using he.symm
    _ = _ := (planarSphereProjector_hasDerivAt z w).deriv

/-- The descended actual projective projector is idempotent at every point. -/
theorem planarProjectiveProjector_idempotent {C : ℕ} (x : PlanarRealProjective C) :
    IsIdempotentElem (planarProjectiveProjector x) := by
  induction x using Quotient.inductionOn with
  | _ z => exact planarSphereProjector_idempotent z

/-- The actual projective projector has real rank one everywhere. -/
theorem planarProjectiveProjector_finrank {C : ℕ} (x : PlanarRealProjective C) :
    Module.finrank ℝ (planarProjectiveProjector x).toLinearMap.range = 1 := by
  induction x using Quotient.inductionOn with
  | _ z => exact planarSphereProjector_finrank z

/-- The projector applied to its actual generator derivative has the precise scalar
lift expression; tangency removes the extra radius term. -/
theorem planarSphereProjector_project_derivative {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) (w : PlanarHopfAmbient C) :
    planarSphereProjector z
      (mvfderiv (planarHopfModel C) planarSphereProjector z (planarHopfGenerator z) w) =
      ⟪((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)), w⟫ •
        (z : PlanarHopfAmbient C) := by
  rw [planarSphereProjector_mvfderiv_apply]
  simp only [planarSphereProjector_apply, inner_add_right, real_inner_smul_right,
    planarHopfVelocity_orthogonal, mul_zero, zero_add, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp z.property, one_pow, mul_one]

end GlobalEmbedding.Paper
