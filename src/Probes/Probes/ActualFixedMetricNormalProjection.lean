import GlobalEmbedding.Paper.NormalProjectionGramFormula
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Module
import Mathlib.Tactic.GCongr

/-!
# Native normal-projection parameter response for an actual fixed metric

The projection is the ORIGINAL orthogonal projection onto the actual frame's
normal space. A fixed induced Gram metric makes its inverse constant; native
product and adjoint derivatives therefore compute the projection response
without an assumed projection-derivative formula. The actual normal projection
has an O(first-jet-response) bound, which is the O(delta) input to prop:probes.
-/
noncomputable section
open GlobalEmbedding.Paper Filter
open scoped Topology
namespace GlobalEmbedding.Offline

variable {P D V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Native parameter derivative of the original normal projection under a
fixed actual Gram metric. The right side uses the actual derivative of A. -/
theorem fderiv_actualNormalProjection_fixed_metric
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀) :
    fderiv ℝ (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a =
      -((fderiv ℝ A u a).comp ((A₀.adjoint.comp A₀).inverse.comp (A u).adjoint)) -
        (A u).comp ((A₀.adjoint.comp A₀).inverse.comp (fderiv ℝ A u a).adjoint) := by
  let G := (A₀.adjoint.comp A₀).inverse
  let adj : (D →L[ℝ] V) →L[ℝ] (V →L[ℝ] D) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := D) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj := adj.hasFDerivAt.comp u hA.hasFDerivAt
  have hprod := hA.hasFDerivAt.clm_comp ((hasFDerivAt_const G u).clm_comp hadj)
  have hpoly := (hasFDerivAt_const (ContinuousLinearMap.id ℝ V) u).sub hprod
  change HasFDerivAt (fun z ↦ ContinuousLinearMap.id ℝ V -
    (A z).comp (G.comp (A z).adjoint)) _ u at hpoly
  have he : (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) =ᶠ[𝓝 u]
      (fun z ↦ ContinuousLinearMap.id ℝ V - (A z).comp (G.comp (A z).adjoint)) := by
    filter_upwards [hinj, hmetric] with z hz hm
    rw [(normal_projection_gram_formula (A z) hz).2.2.2, hm]
  rw [he.fderiv_eq, hpoly.fderiv]
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, Pi.zero_apply, zero_apply, map_zero, zero_add, add_zero,
    ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, G, adj,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  abel

/-- Actual native norm bound on each projection parameter response. -/
theorem norm_fderiv_actualNormalProjection_fixed_metric_apply_le
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀) :
    ‖fderiv ℝ (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖ := by
  rw [fderiv_actualNormalProjection_fixed_metric A A₀ u a hA hinj hmetric]
  calc
    _ ≤ ‖-((fderiv ℝ A u a).comp ((A₀.adjoint.comp A₀).inverse.comp (A u).adjoint))‖ +
        ‖(A u).comp ((A₀.adjoint.comp A₀).inverse.comp (fderiv ℝ A u a).adjoint)‖ :=
      norm_sub_le _ _
    _ ≤ ‖fderiv ℝ A u a‖ * (‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖) +
        ‖A u‖ * (‖(A₀.adjoint.comp A₀).inverse‖ * ‖fderiv ℝ A u a‖) := by
      simp only [norm_neg]
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using
            (ContinuousLinearMap.opNorm_comp_le (A₀.adjoint.comp A₀).inverse (A u).adjoint)) (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using
            (ContinuousLinearMap.opNorm_comp_le (A₀.adjoint.comp A₀).inverse (fderiv ℝ A u a).adjoint)) (norm_nonneg _))
    _ = _ := by ring

/-- The full projection parameter-derivative norm is controlled by the actual
first-jet parameter-derivative norm, with an explicit fixed-metric constant. -/
theorem norm_fderiv_actualNormalProjection_fixed_metric_le
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀) :
    ‖fderiv ℝ (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u‖ ≤
      2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  calc
    _ ≤ 2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖ :=
      norm_fderiv_actualNormalProjection_fixed_metric_apply_le A A₀ u a hA hinj hmetric
    _ ≤ 2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * (‖fderiv ℝ A u‖ * ‖a‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ A u).le_opNorm a) (by positivity)
    _ = _ := by ring

/-- Actual normal projections are close when the actual first jets are close,
with no derivative or smooth identification hypothesis. -/
theorem norm_actualNormalProjection_sub_fixed_metric_le
    (A A₀ : D →L[ℝ] V) (hA : Function.Injective A) (hA₀ : Function.Injective A₀)
    (hmetric : A.adjoint.comp A = A₀.adjoint.comp A₀) :
    ‖(LinearMap.range A.toLinearMap)ᗮ.starProjection -
      (LinearMap.range A₀.toLinearMap)ᗮ.starProjection‖ ≤
      ‖(A₀.adjoint.comp A₀).inverse‖ * (‖A‖ + ‖A₀‖) * ‖A - A₀‖ := by
  let G := (A₀.adjoint.comp A₀).inverse
  have he : (LinearMap.range A.toLinearMap)ᗮ.starProjection -
      (LinearMap.range A₀.toLinearMap)ᗮ.starProjection =
      -((A - A₀).comp (G.comp A.adjoint)) - A₀.comp (G.comp (A - A₀).adjoint) := by
    rw [(normal_projection_gram_formula A hA).2.2.2,
      (normal_projection_gram_formula A₀ hA₀).2.2.2, hmetric]
    ext v
    simp only [sub_apply, neg_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖-((A - A₀).comp (G.comp A.adjoint))‖ + ‖A₀.comp (G.comp (A - A₀).adjoint)‖ :=
      norm_sub_le _ _
    _ ≤ ‖A - A₀‖ * (‖G‖ * ‖A‖) + ‖A₀‖ * (‖G‖ * ‖A - A₀‖) := by
      simp only [norm_neg]
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using (ContinuousLinearMap.opNorm_comp_le G A.adjoint))
            (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using (ContinuousLinearMap.opNorm_comp_le G (A - A₀).adjoint))
            (norm_nonneg _))
    _ = _ := by dsimp [G]; ring

#print axioms fderiv_actualNormalProjection_fixed_metric
#print axioms norm_fderiv_actualNormalProjection_fixed_metric_le
#print axioms norm_actualNormalProjection_sub_fixed_metric_le
end GlobalEmbedding.Offline
