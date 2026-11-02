import NormalPolar.JointSecondaryNativeGood
import Probes.ActualIncrementPhysicalChartRows

/-! Actual smooth immersion data manufacture the native continuous second
form. A genuine phase derivative is identified with its original manifold
covector by the actual chain rule. No second-form continuity or native Good
predicate is introduced as an original input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped TensorProduct Topology ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativeSmoothRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativeSmoothSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

private local instance nativeSmoothFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance nativeSmoothFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance nativeSmoothVVNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance nativeSmoothVVSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance nativeSmoothHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothIntermediateNormed :
    NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothIntermediateSpace :
    NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance

theorem jointSecondary_native_phase_operator_smooth
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (jointSecondaryNativePhaseOperator F e) e.target := by
  have hFs : ContDiffOn ℝ ∞ (F ∘ e.symm) e.target :=
    (hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  have hA : ContDiffOn ℝ ∞ (fderiv ℝ (F ∘ e.symm)) e.target :=
    hFs.fderiv_of_isOpen e.open_target (by simp)
  have hH : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (F ∘ e.symm))) e.target :=
    hA.fderiv_of_isOpen e.open_target (by simp)
  have hAi : ∀ y ∈ e.target, Injective (fderiv ℝ (F ∘ e.symm) y) :=
    fun y hy => actual_increment_chart_derivative_injective F hF e he y hy (hImm _)
  have hN : ContDiffOn ℝ ∞
      (fun y => (normalSpace (I := IM) F (e.symm y)).starProjection) e.target := by
    apply (smooth_frame_normal_projection _ hA hAi).congr
    intro y hy
    rw [actual_increment_normalSpace_eq_chart_range F hF e he y hy]
  have hQ : ContDiffOn ℝ ∞ (fun y => actualIncrementPostcomposeHessian D V
      (normalSpace (I := IM) F (e.symm y)).starProjection
      (fderiv ℝ (fderiv ℝ (F ∘ e.symm)) y)) e.target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact hN.clm_apply ((hH.clm_apply (contDiffOn_const (c := v))).clm_apply
      (contDiffOn_const (c := w)))
  exact (actualHessianLift (E := D) (F := V)).contDiff.comp_contDiffOn hQ

theorem jointSecondary_native_phase_gradient
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (psi : M → ℝ) (y : D) (hy : y ∈ e.target)
    (hpsi : MDifferentiableAt IM 𝓘(ℝ,ℝ) psi (e.symm y)) :
    fderiv ℝ (psi ∘ e.symm) y =
      (mfderiv IM 𝓘(ℝ,ℝ) psi (e.symm y)).comp (jointSecondaryNativeTangentMap e y) := by
  have h := mfderiv_comp y hpsi
    ((actual_increment_maximal_chart_mdifferentiable e he).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at h
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L => tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (e.symm y))
    (L ((tangentSpaceCastModel IM y).symm v))) h

theorem jointSecondary_native_phase_good_iff
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (psi : M → ℝ) (y : D) (hy : y ∈ e.target)
    (hpsi : MDifferentiableAt IM 𝓘(ℝ,ℝ) psi (e.symm y)) :
    LinearSecondFormGoodCovector (jointSecondaryNativePhaseOperator F e y).toLinearMap
      (fderiv ℝ (psi ∘ e.symm) y).toLinearMap ↔
      GoodCovector F hF (e.symm y) (mfderiv IM 𝓘(ℝ,ℝ) psi (e.symm y)) := by
  rw [jointSecondary_native_phase_gradient e he psi y hy hpsi]
  exact jointSecondary_native_good_iff F hF e he y hy _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_phase_operator_smooth
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_phase_good_iff
