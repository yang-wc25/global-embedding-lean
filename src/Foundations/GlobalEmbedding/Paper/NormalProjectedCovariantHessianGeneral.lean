import GlobalEmbedding.Paper.GeneralTangentCoordinates
import GlobalEmbedding.Paper.GeneralPushedFieldCoordinates
import GlobalEmbedding.Paper.GeneralTangentCenteredValue
import GlobalEmbedding.Paper.ProjectedPushforwardDerivative
import GlobalEmbedding.Paper.NormalProjectionGeneralChartDerivative
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- For arbitrary model I and actual boundaryless source M, the normal-projected
covariant Hessian equals the centered coordinate Hessian for every connection.
All field-coordinate identities and differentiability are derived, not assumed.
Source: `defn:phase`, independence of the chosen torsion-free connection. -/
theorem normal_projected_covariant_hessian_general
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (V : ∀ z : M, TangentSpace I z)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x)
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x)
    (v : TangentSpace I x) :
    let push : M → EuclideanSpace ℝ (Fin N) := fun z ↦
      tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f z)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f z (V z))
    (normalSpace (I := I) f x).starProjection
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (push x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) push x v) -
        tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x (cov V x v))) =
    (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x (V x))) := by
  dsimp only
  let push : M → EuclideanSpace ℝ (Fin N) := fun z ↦
    tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f z)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f z (V z))
  let Y : E → E := fun z ↦ (trivializationAt E (TangentSpace I) x
    ⟨(extChartAt I x).symm z, V ((extChartAt I x).symm z)⟩).2
  have hY : DifferentiableAt ℝ Y (extChartAt I x x) :=
    tangent_section_general_chart_coordinates_differentiable V x hV
  have hcoord : (push ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      (fun y ↦ fderiv ℝ (f ∘ (extChartAt I x).symm) y (Y y)) :=
    pushed_tangent_field_general_chart_eventually f V x hf
  have hfc := contDiffAt_general_chart_representative hf
  have hd : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ (f ∘ (extChartAt I x).symm) y (Y y)) (extChartAt I x x) :=
    ((hfc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply hY
  have hpc : DifferentiableAt ℝ (push ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    hd.congr_of_eventuallyEq hcoord
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have heq : push =ᶠ[𝓝 x] (push ∘ (extChartAt I x).symm) ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with p hp
    change push p = push ((extChartAt I x).symm ((extChartAt I x) p))
    rw [(extChartAt I x).left_inv hp]
  have hpd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) push x :=
    (hpc.mdifferentiableAt.comp x hchart).congr_of_eventuallyEq heq
  have hp : (normalSpace (I := I) f x).starProjection
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x (cov V x v))) = 0 := by
    rw [Submodule.starProjection_apply, normal_projection_mfderiv_eq_zero]
    rfl
  rw [map_sub, hp, sub_zero]
  have hr : Set.range I ∈ 𝓝 (extChartAt I x x) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (x := x))
  have hdpush : tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (push x)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) push x v) =
      fderiv ℝ (push ∘ (extChartAt I x).symm) (extChartAt I x x)
        (tangentSpaceCastModel I x v) := by
    rw [← fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := push ∘ (extChartAt I x).symm) hr]
    simp [mfderiv, hpd, writtenInExtChartAt]
  rw [hdpush, hcoord.fderiv_eq]
  have hP : ∀ z : E, (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) z) = 0 := by
    intro z
    rw [Submodule.starProjection_apply,
      normal_projection_general_chart_derivative f x (hf.mdifferentiableAt (by norm_num)) z]
    rfl
  have hy : Y (extChartAt I x x) = tangentSpaceCastModel I x (V x) :=
    tangent_section_general_centered_value V x
  rw [← hy]
  exact general_projected_derivative_of_pushforward (f ∘ (extChartAt I x).symm) Y
    (normalSpace (I := I) f x).starProjection (extChartAt I x x) hfc hY hP
    (tangentSpaceCastModel I x v)

end GlobalEmbedding.Paper
