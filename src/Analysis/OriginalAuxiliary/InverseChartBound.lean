import Repair.ReferenceAuxiliaryGeometry
import Initialization.Geometry.PreparedCharts

/-!
# Manufactured inverse-chart bounds in the original auxiliary metric

A continuous fixed Riemannian bundle and a fixed smooth chart give an
inverse-derivative bound on a compact coordinate core. This is the missing
direction needed to carry the actual initialization margin back to the
original intrinsic tangent norm. It is selected from the fixed parent
geometry, before any frequency, refined chart family or reference map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization Manifold IsManifold
  Set Function Filter Bundle
open scoped ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.OriginalAuxiliary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, D)

/-- An actual Euclidean-to-manifold derivative is locally bounded in the
fixed continuous auxiliary norm; the derivative itself is not an input. -/
theorem auxiliary_target_mfderiv_locally_bounded
    (f : D → M) (y : D) (hf : ContMDiffAt I I ∞ f y) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 y, ‖mfderiv I I f z‖ ≤ C := by
  let H : D → D →L[ℝ] D := inTangentCoordinates I I id f (mfderiv I I f) y
  have hH : ContinuousAt H y := (hf.mfderiv_const (m := 0) (by simp)).continuousAt
  have hHb : ∀ᶠ z in 𝓝 y, ‖H z‖ < ‖H y‖ + 1 :=
    hH.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨C, hC, hCb⟩ := eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I (f y)
  have hCb' := hf.continuousAt.eventually hCb
  have hSource := hf.continuousAt.eventually (chart_source_mem_nhds D (f y))
  refine ⟨C * (‖H y‖ + 1), mul_pos hC (by positivity), ?_⟩
  filter_upwards [hHb, hCb', hSource] with z hz hCz hzs
  have hid : mfderivWithin I I (extChartAt I y).symm (range I)
      (extChartAt I y z) = ContinuousLinearMap.id ℝ D := by
    rw [show range I = (univ : Set D) from Set.range_id]
    change mfderivWithin I I id univ z = _
    rw [mfderivWithin_univ, mfderiv_id]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hRep : H z = (mfderiv I I (extChartAt I (f y)) (f z)).comp
      (mfderiv I I f z) := by
    have h := inTangentCoordinates_eq_mfderiv_comp_abuse
      («I» := I) (I' := I) (f := id) (g := f) (ϕ := mfderiv I I f)
      (x₀ := y) (x := z) (by simp) hzs
    simp only [id_eq] at h
    rw [hid] at h
    exact h.trans (by apply ContinuousLinearMap.ext; intro v; rfl)
  have hzsExt : f z ∈ (extChartAt I (f y)).source := by
    rw [extChartAt_source]
    exact hzs
  have hInvPoint : (extChartAt I (f y)).symm (extChartAt I (f y) (f z)) = f z :=
    (extChartAt I (f y)).left_inv hzsExt
  have hFactor : mfderiv I I f z =
      (mfderivWithin I I (extChartAt I (f y)).symm (range I) (extChartAt I (f y) (f z))).comp
        (H z) := by
    rw [hRep, ← ContinuousLinearMap.comp_assoc,
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hzsExt,
      ContinuousLinearMap.id_comp]
  rw [hFactor]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul _ hz.le (norm_nonneg _) hC.le
  convert! hCz.le using 1 <;> congr <;> exact hInvPoint.symm

/-- The actual inverse-chart differential is bounded on a compact core
of its unchanged target. -/
theorem auxiliary_inverse_chart_bound
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas I ∞ M)
    (K : Set D) (hK : IsCompact K) (hTarget : K ⊆ e.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ‖mfderiv I I e.symm y‖ ≤ C := by
  apply repair_auxiliary_compact_bound K hK (fun y ↦ ‖mfderiv I I e.symm y‖)
  intro y hy
  obtain ⟨C, _, hC⟩ := auxiliary_target_mfderiv_locally_bounded e.symm y
    (contMDiffAt_symm_of_mem_maximalAtlas he (hTarget hy))
  exact ⟨C, hC⟩

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.auxiliary_target_mfderiv_locally_bounded
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.auxiliary_inverse_chart_bound
