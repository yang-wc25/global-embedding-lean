import Probes.ActualNormalCompression
import Probes.ActualFixedMetricNormalProjection
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Actual parameter response of the normal compression inverse

The compression and inverse are exactly iota-adjoint Pi iota and its native
inverse. Their derivatives are computed, not assumed. Projection closeness
produces invertibility and the inverse constant; the actual fixed-metric frame
response supplies the final O(first-jet-parameter-response) estimate. This does
not construct or identify an inverse square root.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Filter
open scoped Topology
namespace GlobalEmbedding.Offline

section Inverse
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Native parameter derivative of the actual continuous-linear-map inverse. -/
theorem fderiv_native_inverse_apply
    (G : P → W →L[ℝ] W) (u a : P) (hG : DifferentiableAt ℝ G u)
    (hinv : (G u).IsInvertible) :
    fderiv ℝ (fun z ↦ (G z).inverse) u a =
      -((G u).inverse * (fderiv ℝ G u a) * (G u).inverse) := by
  have hu : IsUnit (G u) := (G u).isUnit_iff_bijective.mpr hinv.bijective
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have hs : Ring.inverse (G u) = ↑hu.unit⁻¹ :=
    (congrArg Ring.inverse hu.unit_spec).symm.trans (Ring.inverse_unit hu.unit)
  rw [hu.unit_spec, ← hs] at hi
  have hh := hi.comp u hG.hasFDerivAt
  change HasFDerivAt (fun z ↦ Ring.inverse (G z)) _ u at hh
  simp only [ContinuousLinearMap.ringInverse_eq_inverse] at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
end Inverse

section Compression
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private noncomputable local instance responseAmbientSemi : SeminormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance responseAmbientNormed : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance responseAmbientSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance responseFiberSemi (K : Submodule ℝ V) : SeminormedAddCommGroup (K →L[ℝ] K) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance responseFiberNormed (K : Submodule ℝ V) : NormedAddCommGroup (K →L[ℝ] K) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance responseFiberSpace (K : Submodule ℝ V) : NormedSpace ℝ (K →L[ℝ] K) :=
  ContinuousLinearMap.toNormedSpace

/-- Actual compression differentiation is the original fixed inclusion and
orthogonal projection applied to the actual ambient projection derivative. -/
theorem fderiv_normalProjectionCompression_apply
    (K : Submodule ℝ V) (Pi : P → V →L[ℝ] V) (u a : P)
    (hPi : DifferentiableAt ℝ Pi u) :
    fderiv ℝ (fun z ↦ normalProjectionCompression K (Pi z)) u a =
      normalProjectionCompression K (fderiv ℝ Pi u a) := by
  have h := (normalProjectionCompressionL K).hasFDerivAt.comp u hPi.hasFDerivAt
  change HasFDerivAt (fun z ↦ normalProjectionCompression K (Pi z)) _ u at h
  rw [h.fderiv]
  rfl

/-- The true native inverse compression parameter response is controlled by
the original projection response, with a reserve produced from closeness. -/
theorem norm_fderiv_normalProjectionCompression_inverse_apply_le
    (K : Submodule ℝ V) (Pi : P → V →L[ℝ] V) (u a : P)
    (hPi : DifferentiableAt ℝ Pi u) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hclose : ‖Pi u - K.starProjection‖ ≤ epsilon) :
    ‖fderiv ℝ (fun z ↦ (normalProjectionCompression K (Pi z)).inverse) u a‖ ≤
      ((1 - epsilon)⁻¹) ^ 2 * ‖fderiv ℝ Pi u a‖ := by
  let G : P → K →L[ℝ] K := fun z ↦ normalProjectionCompression K (Pi z)
  have hG : DifferentiableAt ℝ G u :=
    (normalProjectionCompressionL K).differentiableAt.comp u hPi
  obtain ⟨hinv, hbound⟩ := normalProjectionCompression_inverse_bound K (Pi u) epsilon hepsilon hclose
  rw [fderiv_native_inverse_apply G u a hG hinv, norm_neg]
  have hDG : ‖fderiv ℝ G u a‖ ≤ ‖fderiv ℝ Pi u a‖ := by
    rw [fderiv_normalProjectionCompression_apply K Pi u a hPi]
    exact normalProjectionCompression_norm_le K _
  have hb0 : 0 ≤ (1 - epsilon)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hepsilon.le)
  calc
    _ ≤ (‖(G u).inverse‖ * ‖fderiv ℝ G u a‖) * ‖(G u).inverse‖ :=
      by
        change ‖((G u).inverse.comp (fderiv ℝ G u a)).comp (G u).inverse‖ ≤ _
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (((1 - epsilon)⁻¹) * ‖fderiv ℝ Pi u a‖) * ((1 - epsilon)⁻¹) :=
      mul_le_mul (mul_le_mul hbound hDG (norm_nonneg _) hb0) hbound (norm_nonneg _) (by positivity)
    _ = _ := by ring
end Compression

section ActualFrame
variable {P D V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Actual normal projection differentiability follows from the same fixed
metric and actual frame, rather than being supplied by the caller. -/
theorem differentiableAt_actualNormalProjection_fixed_metric
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀) :
    DifferentiableAt ℝ (fun z ↦ (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u := by
  let G := (A₀.adjoint.comp A₀).inverse
  let adj : (D →L[ℝ] V) →L[ℝ] (V →L[ℝ] D) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := D) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have ha := adj.differentiableAt.comp u hA
  have hp := (differentiableAt_const (ContinuousLinearMap.id ℝ V)).sub
    (hA.clm_comp ((differentiableAt_const G).clm_comp ha))
  change DifferentiableAt ℝ (fun z ↦ ContinuousLinearMap.id ℝ V -
    (A z).comp (G.comp (A z).adjoint)) u at hp
  apply hp.congr_of_eventuallyEq
  filter_upwards [hinj, hmetric] with z hz hm
  rw [(normal_projection_gram_formula (A z) hz).2.2.2, hm]

/-- The actual normal compression inverse inherits O(D_u D_x F), with no
assumed projection or inverse response formula. This is a true prerequisite
for the later inverse-square-root normal identification. -/
theorem norm_fderiv_actualNormalCompression_inverse_apply_le
    (K : Submodule ℝ V) (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : P)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hclose : ‖(LinearMap.range (A u).toLinearMap)ᗮ.starProjection - K.starProjection‖ ≤ epsilon) :
    ‖fderiv ℝ (fun z ↦ (normalProjectionCompression K
      (LinearMap.range (A z).toLinearMap)ᗮ.starProjection).inverse) u a‖ ≤
      ((1 - epsilon)⁻¹) ^ 2 *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  apply (norm_fderiv_normalProjectionCompression_inverse_apply_le K _ u a
    (differentiableAt_actualNormalProjection_fixed_metric A A₀ u hA hinj hmetric)
    epsilon hepsilon hclose).trans
  exact mul_le_mul_of_nonneg_left
    (norm_fderiv_actualNormalProjection_fixed_metric_apply_le A A₀ u a hA hinj hmetric)
    (sq_nonneg _)

/-- The genuine old normal space and actual first-jet gap themselves produce
all projection-closeness data for the inverse response. No separate normal
projection or inverse bound occurs among the hypotheses. -/
theorem norm_fderiv_actualNormalCompression_inverse_from_frame_gap_le
    (A : P → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : P)
    (hA : DifferentiableAt ℝ A u) (hinj₀ : Function.Injective A₀)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (hgap : ‖(A₀.adjoint.comp A₀).inverse‖ * (‖A u‖ + ‖A₀‖) * ‖A u - A₀‖ < 1) :
    let epsilon := ‖(A₀.adjoint.comp A₀).inverse‖ * (‖A u‖ + ‖A₀‖) * ‖A u - A₀‖
    ‖fderiv ℝ (fun z ↦ (normalProjectionCompression (LinearMap.range A₀.toLinearMap)ᗮ
      (LinearMap.range (A z).toLinearMap)ᗮ.starProjection).inverse) u a‖ ≤
      ((1 - epsilon)⁻¹) ^ 2 *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  exact norm_fderiv_actualNormalCompression_inverse_apply_le (LinearMap.range A₀.toLinearMap)ᗮ
    A A₀ u a hA hinj hmetric _ hgap
    (norm_actualNormalProjection_sub_fixed_metric_le (A u) A₀ hinj.self_of_nhds hinj₀ hmetric.self_of_nhds)

end ActualFrame
#print axioms fderiv_native_inverse_apply
#print axioms norm_fderiv_normalProjectionCompression_inverse_apply_le
#print axioms norm_fderiv_actualNormalCompression_inverse_apply_le
#print axioms norm_fderiv_actualNormalCompression_inverse_from_frame_gap_le
end GlobalEmbedding.Offline
