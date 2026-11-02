import Probes.ActualIncrementKernelCoordinates

/-!
# Chosen-phase transverse reserve from the actual maximal chart

The inverse-chart tangent equivalence and its zero-first kernel coordinates
are now constructed from the chosen maximal chart. The only conditioning
inputs are the genuine chosen restricted-form margin and the genuine
forward-chart derivative norm. The desired transverse-frame reserve is an
output, with the same fixed dimension-only canonical quotient factor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Bundle
open scoped ContDiff TensorProduct
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance chartMarginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance chartMarginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_maximal_chart_mdifferentiable
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) : chart.MDifferentiable 𝓙 𝓙 := by
  have h1 : chart ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hchart
  constructor
  · intro q hq
    exact (mdifferentiableAt_of_mem_maximalAtlas h1 hq).mdifferentiableWithinAt
  · intro q hq
    exact (mdifferentiableAt_symm_of_mem_maximalAtlas h1 hq).mdifferentiableWithinAt

def actualIncrementChartDerivativeEquiv
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target) :
    D ≃L[ℝ] TangentSpace 𝓙 (chart.symm x) :=
  (actual_increment_maximal_chart_mdifferentiable chart hchart).symm.mfderiv hx

theorem actualIncrementChartDerivativeEquiv_single
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target)
    (i : Fin (m+1)) :
    actualIncrementChartDerivativeEquiv chart hchart x hx (EuclideanSpace.single i 1) =
      incrementsModeCoordinateDirections chart.symm x i := rfl

theorem actualIncrementChartDerivativeEquiv_symm
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target) :
    (actualIncrementChartDerivativeEquiv chart hchart x hx).symm.toContinuousLinearMap =
      mfderiv 𝓙 𝓙 chart (chart.symm x) := rfl

variable [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

private local instance chartTangentNormed (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance chartTangentSpace (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance chartTangentInner (x : M) : InnerProductSpace ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance

/-- An actual selected chart and the margin of its actual transported first
covector supply the original frame reserve. No kernel-equivalence, coordinate
identity, transverse Gram estimate, or desired inverse bound is an input. -/
theorem actual_increment_chart_frame_reserve
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D) (hx : x ∈ chart.target)
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hforward : ‖(tangentSpaceCastModel 𝓙 (chart (chart.symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓙 chart (chart.symm x))‖^2 ≤ C)
    (hmargin : let xi := (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x))
      ∀ w : SymmetricSquare xi.ker, eta * ‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL F hF (chart.symm x)) xi w‖)
    (t : Tdata) :
    (eta / (C * actualIncrementSortedSymmetricConstant m))^2 * ‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF chart.symm x t‖^2 := by
  let A := actualIncrementChartDerivativeEquiv chart hchart x hx
  let xi := (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x))
  let e : D0 ≃L[ℝ] xi.ker := actualIncrementCoordinateKernelEquiv A
  have he (a : Fin m) : ((e (EuclideanSpace.single a 1)) : TangentSpace 𝓙 (chart.symm x)) =
      incrementsModeCoordinateDirections chart.symm x a.succ := by
    exact actualIncrementCoordinateKernelEquiv_single A a
  have hi : ‖e.symm.toContinuousLinearMap‖^2 ≤ C := by
    have hb : ‖e.symm.toContinuousLinearMap‖ ≤ ‖A.symm.toContinuousLinearMap‖ :=
      actualIncrementCoordinateKernelEquiv_inverse_norm A
    have hAE : A.symm.toContinuousLinearMap =
        (tangentSpaceCastModel 𝓙 (chart (chart.symm x))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓙 chart (chart.symm x)) := by
      ext v
      rfl
    have hfwd : ‖A.symm.toContinuousLinearMap‖^2 ≤ C := by
      rw [hAE]
      exact hforward
    exact (sq_le_sq₀ e.symm.toContinuousLinearMap.opNorm_nonneg
      A.symm.toContinuousLinearMap.opNorm_nonneg |>.mpr hb).trans hfwd
  exact actual_increment_frame_reserve_of_chosen_margin F hF chart.symm x xi e he
    eta C heta hC hi hmargin t

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualIncrementChartDerivativeEquiv
#print axioms GlobalEmbedding.Continuation.actual_increment_chart_frame_reserve
