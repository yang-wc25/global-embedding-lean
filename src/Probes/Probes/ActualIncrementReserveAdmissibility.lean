import Probes.ActualIncrementPhysicalChartRows
import Probes.ActualIncrementChartMarginReserve
import Smoothing.WeightedActualProjection

/-!
# Genuine geometric reserves supply the original admissibility conditions

The native first-frame reserve gives injectivity of the original manifold
derivative in the same maximal chart. The native transverse-frame reserve
gives invertibility of the original beta Gram by its exact ambient identity.
These are consumers of genuine primitive reserves, not new admissibility
or inverse hypotheses on the desired mode.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- Exact native chart expression of the original manifold derivative. -/
theorem actual_increment_coordinate_first_derivative_eq
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target) :
    fderiv ℝ (F ∘ chart.symm) x =
      ((tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x))).comp
          (mfderiv 𝓙 𝓙 chart.symm x) := by
  have hc := (actual_increment_maximal_chart_mdifferentiable chart hchart).mdifferentiableAt_symm hx
  have h := mfderiv_comp x (hF.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at h
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L => tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))
    (L ((tangentSpaceCastModel 𝓙 x).symm v))) h

/-- A true native source reserve implies injectivity of the actual original
manifold derivative, not only of a replacement coordinate map. -/
theorem actual_increment_manifold_injective_of_first_reserve
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target)
    (c : ℝ) (hc : 0 < c)
    (hreserve : ∀ v : D, c * ‖v‖^2 ≤ ‖fderiv ℝ (F ∘ chart.symm) x v‖^2) :
    Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x)) := by
  have hi := actual_frame_injective_of_reserve (fderiv ℝ (F ∘ chart.symm) x) c hc hreserve
  rw [actual_increment_coordinate_first_derivative_eq F hF chart hchart x hx] at hi
  let A := actualIncrementChartDerivativeEquiv chart hchart x hx
  intro u v huv
  apply A.symm.injective
  apply hi
  change tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x) (A (A.symm u))) =
    tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x) (A (A.symm v)))
  rw [A.apply_symm_apply, A.apply_symm_apply, huv]

/-- The same true transverse reserve supplies invertibility of the original
beta Gram via the exact original ambient-frame Gram identity. -/
theorem actual_increment_transverse_gram_of_reserve
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : D → M) (x : D)
    (cT : ℝ) (hcT : 0 < cT)
    (hreserve : ∀ v : Tdata, cT * ‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF chart x v‖^2) :
    let beta := incrementsTransversePairing F hF (chart x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart x a.succ)
    (beta.comp beta.adjoint).IsInvertible := by
  have hi := actual_frame_injective_of_reserve
    (incrementsModeAmbientTransverseFrame F hF chart x) cT hcT hreserve
  have hg := (frame_gram_positive_invertible
    (incrementsModeAmbientTransverseFrame F hF chart x) hi).2.2
  rwa [incrementsModeAmbientTransverseFrame_gram] at hg

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_manifold_injective_of_first_reserve
#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_gram_of_reserve
