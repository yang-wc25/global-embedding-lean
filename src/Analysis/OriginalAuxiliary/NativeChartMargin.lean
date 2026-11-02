import Initialization.Phase.NativeChartPhase
import Repair.IncrementOriginalPhaseMargin
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The original intrinsic margin and the actual initialization chart margin

This is the quantitative form of the already accepted exact second-form
chart identity. The target normal inclusion is isometric and the source
auxiliary norm is retained. The geometric inverse bound is manufactured
from fixed parent charts in `PreparedParentBounds` before it is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set
open scoped ContDiff TensorProduct
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.OriginalAuxiliary
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance nativeRelationsClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private noncomputable local instance nativeSquareNormed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)] {N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- Actual inverse-chart comparison, preserving the auxiliary norm. -/
theorem chart_margin_to_original_native
    (hdim : 2 ≤ Module.finrank ℝ E)
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) (C : ℝ) (hC : 0 < C)
    (hInverse : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)‖^2 ≤ C) :
    chartPhaseMargin (H ∘ e.symm) (e x) / C ≤ truePhaseMargin H hH x := by
  let A := initializationChartTangentEquiv e he x hx
  let B := chartNormalSecondJet (H ∘ e.symm) (e x)
  let Q := (normalSpace (I := 𝓘(ℝ, E)) H x).subtypeL.comp (trueSecondFormL H hH x)
  have hA : A = (initialization_chart_mdifferentiable e he).mfderiv hx := by
    ext v
    rfl
  have hInv : ‖A.symm.toContinuousLinearMap‖^2 ≤ C := by
    let L : E →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)
    have hAL : A.symm.toContinuousLinearMap = L := by
      rw [hA]
      rfl
    rw [hAL]
    convert! hInverse using 1 <;> congr <;> exact (e.left_inv hx).symm
  have hQB : Q = B.comp (symmetricSquareMapL A.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    have ht := (congrArg (fun L ↦ L z)
      (initialization_chart_trueSecondForm H hH e he x hx)).symm
    change Q z = B (symmetricSquareMapL A.toContinuousLinearMap z)
    rw [symmetricSquareMapL_apply, ← symmetric_square_linear_map_eq A.toContinuousLinearMap]
    exact ht
  have hMargin : bestPhaseSupremum Q = truePhaseMargin H hH x :=
    (true_phase_margin_specification hdim H hH x).2.2.2 Q rfl
  have h := increment_best_phase_supremum_transport hdim A Q B hQB C hC hInv
  simpa only [hMargin, B, chartPhaseMargin] using h

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.chart_margin_to_original_native
