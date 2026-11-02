import Probes.ActualOriginalUnitFreeNormal

/-! Original immersion is a consequence of the genuine native first-frame
reserve in the actual maximal chart. This converse avoids retaining an
independent new-map immersion hypothesis after two-jet stability. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Filter
open scoped Topology ContDiff
namespace GlobalEmbedding.Continuation

section ActualChart

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Cdata" => Fin (m + 1) → ℂ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

theorem actual_increment_immersion_of_chart_derivative_injective
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (heChart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target)
    (hinj : Function.Injective (fderiv ℝ (F ∘ chart.symm) x)) :
    Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x)) := by
  have ha1 : chart ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) heChart
  have hac : chart.MDifferentiable 𝓙 𝓙 := by
    constructor
    · intro q hq
      exact (mdifferentiableAt_of_mem_maximalAtlas ha1 hq).mdifferentiableWithinAt
    · intro q hq
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas ha1 hq).mdifferentiableWithinAt
  have hpush : fderiv ℝ (F ∘ chart.symm) x =
      ((tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x))).comp
          (mfderiv 𝓙 𝓙 chart.symm x) := by
    have hc := hac.mdifferentiableAt_symm hx
    have h := mfderiv_comp x (hF.mdifferentiable (by simp) _) hc
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))
      (L ((tangentSpaceCastModel 𝓙 x).symm v))) h
  intro u v huv
  obtain ⟨a,ha⟩ := (hac.symm.mfderiv hx).surjective u
  obtain ⟨b,hb⟩ := (hac.symm.mfderiv hx).surjective v
  change mfderiv 𝓙 𝓙 chart.symm x a = u at ha
  change mfderiv 𝓙 𝓙 chart.symm x b = v at hb
  rw [← ha,← hb] at huv ⊢
  apply congrArg (mfderiv 𝓙 𝓙 chart.symm x)
  apply hinj
  rw [hpush]
  exact congrArg (tangentSpaceCastModel 𝓘(ℝ,V) (F (chart.symm x))) huv


theorem actual_increment_immersion_of_chart_reserve
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (he : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target) (c : ℝ) (hc : 0 < c)
    (hReserve : ∀ w : D, c*‖w‖^2 ≤ ‖fderiv ℝ (F ∘ chart.symm) x w‖^2) :
    Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) F (chart.symm x)) :=
  actual_increment_immersion_of_chart_derivative_injective F hF chart he x hx
    (actual_frame_injective_of_reserve _ c hc hReserve)

end ActualChart
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_increment_immersion_of_chart_derivative_injective
#print axioms GlobalEmbedding.Continuation.actual_increment_immersion_of_chart_reserve
