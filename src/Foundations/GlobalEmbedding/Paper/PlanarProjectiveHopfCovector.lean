import GlobalEmbedding.Paper.PlanarProjectiveHopfGenerator
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import GlobalEmbedding.Paper.BalancedDirectionalCalculus

/-!
# An actual smooth normalized projective Hopf covector

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-projective-hopf-covector`.
-/
noncomputable section
open Manifold
open scoped ContDiff RealInnerProductSpace
open Bundle (TotalSpace)
namespace GlobalEmbedding.Paper

/-- A genuine Euclidean coordinate space for the finite-dimensional real endomorphisms.
No inner product on the operator-norm space is assumed. -/
abbrev PlanarProjectorCoordinates (C : ℕ) := EuclideanSpace ℝ
  (Fin (Module.finrank ℝ (PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C)))

/-- An actual continuous real-linear coordinate equivalence, obtained from equality
of the genuine finite dimensions. -/
def planarProjectorCoordinateEquiv (C : ℕ) :
    (PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C) ≃L[ℝ] PlanarProjectorCoordinates C :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The actual smooth projective projector viewed in genuine Euclidean coordinates. -/
def planarProjectorCoordinateMap {C : ℕ} (x : PlanarRealProjective C) :
    PlanarProjectorCoordinates C := planarProjectorCoordinateEquiv C (planarProjectiveProjector x)

/-- The coordinate choice preserves actual native smoothness. -/
theorem planarProjectorCoordinateMap_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarProjectorCoordinates C) ∞
      (@planarProjectorCoordinateMap C) :=
  (planarProjectorCoordinateEquiv C).contDiff.contMDiff.comp (planarProjectiveProjector_contMDiff C)

/-- The genuine derivative of the actual Euclidean coordinate map on native vectors. -/
def planarProjectorCoordinateDifferential {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) :
    TangentSpace (planarHopfModel C) x →L[ℝ] PlanarProjectorCoordinates C :=
  mvfderiv (planarHopfModel C) planarProjectorCoordinateMap x

/-- The actual total-space differential is native smooth, by tangent-map smoothness. -/
theorem planarProjectorCoordinateDifferential_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C).tangent 𝓘(ℝ, PlanarProjectorCoordinates C) ∞
      (fun v : TangentBundle (planarHopfModel C) (PlanarRealProjective C) ↦
        planarProjectorCoordinateDifferential v.proj v.2) :=
  (contMDiff_snd_tangentBundle_modelSpace (PlanarProjectorCoordinates C)
    𝓘(ℝ, PlanarProjectorCoordinates C)).comp
      ((planarProjectorCoordinateMap_contMDiff C).contMDiff_tangentMap (by simp))

/-- The true derivative of the coordinate map along the genuine projective Hopf field. -/
def planarProjectorCoordinateVelocity {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) : PlanarProjectorCoordinates C :=
  planarProjectorCoordinateDifferential x (planarProjectiveHopfGenerator x)

/-- The actual velocity observable is native smooth. -/
theorem planarProjectorCoordinateVelocity_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarProjectorCoordinates C) ∞
      (@planarProjectorCoordinateVelocity C _) :=
  balanced_directional_contMDiff planarProjectorCoordinateMap
    (planarProjectorCoordinateMap_contMDiff C) (planarProjectiveHopfGeneratorSection C)

/-- The actual coordinate differential is the fixed real-linear equivalence applied
to the actual projective projector derivative. -/
theorem planarProjectorCoordinateVelocity_eq {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) :
    planarProjectorCoordinateVelocity x = planarProjectorCoordinateEquiv C
      (mvfderiv (planarHopfModel C) planarProjectiveProjector x
        (planarProjectiveHopfGenerator x)) := by
  have h := mvfderiv_comp (I' := planarHopfModel C)
    (I := 𝓘(ℝ, PlanarHopfAmbient C →L[ℝ] PlanarHopfAmbient C)) x
    (((planarProjectorCoordinateEquiv C).contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
    ((planarProjectiveProjector_contMDiff C).mdifferentiableAt (by simp))
  have he := congrArg (fun T ↦ T (planarProjectiveHopfGenerator x)) h
  rw [mvfderiv_eq_fderiv] at he
  change planarProjectorCoordinateVelocity x =
    fderiv ℝ (planarProjectorCoordinateEquiv C) (planarProjectiveProjector x)
      (mvfderiv (planarHopfModel C) planarProjectiveProjector x
        (planarProjectiveHopfGenerator x)) at he
  rw [ContinuousLinearEquiv.fderiv] at he
  exact he

/-- The coordinate observable has genuinely nonzero derivative along the actual
Hopf field: its underlying projector derivative sends the radius to the nonzero
actual ambient Hopf velocity. -/
theorem planarProjectorCoordinateVelocity_ne_zero {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) : planarProjectorCoordinateVelocity x ≠ 0 := by
  obtain ⟨z, rfl⟩ := planarAntipodalProjection_surjective C x
  rw [planarProjectorCoordinateVelocity_eq]
  intro hzero
  have hd : mvfderiv (planarHopfModel C) planarProjectiveProjector
      (planarAntipodalProjection z)
      (planarProjectiveHopfGenerator (planarAntipodalProjection z)) = 0 :=
    (planarProjectorCoordinateEquiv C).injective (hzero.trans (map_zero _).symm)
  have he := planarProjectiveProjector_mvfderiv_apply z (z : PlanarHopfAmbient C)
  rw [hd, zero_apply] at he
  have hvz := planarHopfVelocity_orthogonal z
  rw [real_inner_comm] at hvz
  simp only [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp z.property,
    one_pow, one_smul, hvz, zero_smul, add_zero] at he
  exact (smul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))
      Complex.I_ne_zero) (ne_zero_of_mem_unit_sphere z)) he.symm

/-- The genuine normalized cotangent functional, obtained from the actual Euclidean
projector observable. It requires no chosen metric or formal coframe on RP. -/
def planarProjectiveHopfCovector {C : ℕ} [Fact (0 < C)] (x : PlanarRealProjective C) :
    TangentSpace (planarHopfModel C) x →L[ℝ] ℝ :=
  (‖planarProjectorCoordinateVelocity x‖ ^ 2)⁻¹ •
    (innerSL ℝ (planarProjectorCoordinateVelocity x)).comp
      (planarProjectorCoordinateDifferential x)

/-- The actual cotangent functional takes value one on the actual projective generator. -/
@[simp] theorem planarProjectiveHopfCovector_generator {C : ℕ} [Fact (0 < C)]
    (x : PlanarRealProjective C) :
    planarProjectiveHopfCovector x (planarProjectiveHopfGenerator x) = 1 := by
  change (‖planarProjectorCoordinateVelocity x‖ ^ 2)⁻¹ *
    ⟪planarProjectorCoordinateVelocity x, planarProjectorCoordinateVelocity x⟫ = 1
  rw [real_inner_self_eq_norm_sq]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (planarProjectorCoordinateVelocity_ne_zero x)))

/-- The genuine reciprocal normalizing factor is native smooth, because the actual
Euclidean velocity is nowhere zero. -/
theorem planarProjectorCoordinateVelocity_invNormSq_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun x : PlanarRealProjective C ↦ (‖planarProjectorCoordinateVelocity x‖ ^ 2)⁻¹) := by
  have hi : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun x : PlanarRealProjective C ↦
        ⟪planarProjectorCoordinateVelocity x, planarProjectorCoordinateVelocity x⟫) :=
    ((innerSL ℝ : PlanarProjectorCoordinates C →L[ℝ]
      PlanarProjectorCoordinates C →L[ℝ] ℝ).contDiff.contMDiff.comp
        (planarProjectorCoordinateVelocity_contMDiff C)).clm_apply
          (planarProjectorCoordinateVelocity_contMDiff C)
  have hn : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun x : PlanarRealProjective C ↦ ‖planarProjectorCoordinateVelocity x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using hi
  exact hn.inv₀ (fun x ↦ pow_ne_zero 2
    (norm_ne_zero_iff.mpr (planarProjectorCoordinateVelocity_ne_zero x)))

/-- The actual cotangent functional is smooth as a function on the genuine native
tangent total space. Thus beta is a smooth one-form, not just a pointwise covector. -/
theorem planarProjectiveHopfCovector_contMDiff_eval (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C).tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle (planarHopfModel C) (PlanarRealProjective C) ↦
        planarProjectiveHopfCovector v.proj v.2) := by
  have hp : ContMDiff (planarHopfModel C).tangent (planarHopfModel C) ∞
      (fun v : TangentBundle (planarHopfModel C) (PlanarRealProjective C) ↦ v.proj) :=
    Bundle.contMDiff_proj (TangentSpace (planarHopfModel C))
  have hu := (planarProjectorCoordinateVelocity_contMDiff C).comp hp
  have hi : ContMDiff (planarHopfModel C).tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle (planarHopfModel C) (PlanarRealProjective C) ↦
        ⟪planarProjectorCoordinateVelocity v.proj,
          planarProjectorCoordinateDifferential v.proj v.2⟫) :=
    ((innerSL ℝ : PlanarProjectorCoordinates C →L[ℝ]
      PlanarProjectorCoordinates C →L[ℝ] ℝ).contDiff.contMDiff.comp hu).clm_apply
        (planarProjectorCoordinateDifferential_contMDiff C)
  exact ((planarProjectorCoordinateVelocity_invNormSq_contMDiff C).comp hp).smul hi

/-- The normalized covector as a genuine native smooth cotangent section. -/
def planarProjectiveHopfCovectorSection (C : ℕ) [Fact (0 < C)] :
    ContMDiffSection (planarHopfModel C)
      (EuclideanSpace ℝ (Fin (2 * C - 1)) →L[ℝ] ℝ) ∞
      (fun x : PlanarRealProjective C ↦ TangentSpace (planarHopfModel C) x →L[ℝ]
        Bundle.Trivial (PlanarRealProjective C) ℝ x) where
  toFun := planarProjectiveHopfCovector
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    apply (manifold_finite_operator_smooth_iff _ x₀).mpr
    intro u
    let e := trivializationAt (EuclideanSpace ℝ (Fin (2 * C - 1)))
      (TangentSpace (planarHopfModel C) : PlanarRealProjective C → Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hxu : (x₀, u) ∈ e.target := by
      exact ⟨hx₀, Set.mem_univ _⟩
    have hframe := (e.contMDiffOn_symm (IB := planarHopfModel C) (n := ∞)).contMDiffAt
      (e.open_target.mem_nhds hxu)
    have hlift := hframe.comp x₀
      (contMDiffAt_id.prodMk (contMDiffAt_const (c := u)))
    have hi := (planarProjectiveHopfCovector_contMDiff_eval C).contMDiffAt.comp x₀ hlift
    apply hi.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
    change ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin (2 * C - 1)))
      (TangentSpace (planarHopfModel C)) ℝ (Bundle.Trivial (PlanarRealProjective C) ℝ)
      x₀ x x₀ x (planarProjectiveHopfCovector x) u =
      planarProjectiveHopfCovector (e.toOpenPartialHomeomorph.symm (x, u)).proj
        (e.toOpenPartialHomeomorph.symm (x, u)).2
    have ht : trivializationAt ℝ (Bundle.Trivial (PlanarRealProjective C) ℝ) x₀ =
        Bundle.Trivial.trivialization (PlanarRealProjective C) ℝ :=
      Bundle.Trivial.eq_trivialization _ _ _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, ht,
      Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
    change planarProjectiveHopfCovector x (e.symmL ℝ x u) = _
    rw [e.symmL_apply hx]
    have he : e.toOpenPartialHomeomorph.symm (x, u) =
        TotalSpace.mk' (EuclideanSpace ℝ (Fin (2 * C - 1))) x (e.symm x u) :=
      (e.mk_symm hx u).symm
    rw [he]


end GlobalEmbedding.Paper
