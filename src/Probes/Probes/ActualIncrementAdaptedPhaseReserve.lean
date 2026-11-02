import Probes.ActualIncrementChartMarginReserve

/-!
# The actual adapted phase supplies the chosen transverse reserve

Differentiate the literal adaptation identity psi(chart.symm z)=z_0 on the
actual open domain. The original manifold phase differential is thereby
identified with the transported first covector used by the kernel producer.
Its own true restricted-form margin supplies the original frame reserve.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance adaptedSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance adaptedSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The genuine original phase differential is exactly the first coordinate
covector transported by the actual adapted maximal chart. -/
theorem actual_increment_phaseCovector_eq_chosen_chart
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0) :
    (tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x)) =
      (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x)) := by
  let c : D → M := chart.symm
  let A : D →L[ℝ] TangentSpace 𝓙 (c x) := mfderiv 𝓙 𝓙 c x
  let H : TangentSpace 𝓙 (c x) →L[ℝ] D := mfderiv 𝓙 𝓙 chart (c x)
  let d : TangentSpace 𝓙 (c x) →L[ℝ] ℝ :=
    (tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (c x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ, ℝ) psi (c x))
  have hc : MDifferentiableAt 𝓙 𝓙 c x :=
    (actual_increment_maximal_chart_mdifferentiable chart hchart).mdifferentiableAt_symm (hOt hx)
  have heq : psi ∘ c =ᶠ[𝓝 x] (fun z : D => z 0) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hx) hadapt
  have hp : fderiv ℝ (psi ∘ c) x = EuclideanSpace.proj 0 :=
    heq.fderiv_eq.trans (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0).fderiv
  have hm := mfderiv_comp x hpsi hc
  rw [mfderiv_eq_fderiv, hp] at hm
  have hchain : d.comp A = EuclideanSpace.proj 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L =>
      tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (c x))
        (L ((tangentSpaceCastModel 𝓙 x).symm v))) hm
    change (EuclideanSpace.proj 0) v = d (A v) at h
    exact h.symm
  have hAH : A.comp H = ContinuousLinearMap.id ℝ (TangentSpace 𝓙 (c x)) := by
    ext v
    exact (actualIncrementChartDerivativeEquiv chart hchart x (hOt hx)).apply_symm_apply v
  change d = (EuclideanSpace.proj 0).comp H
  calc
    d = d.comp (A.comp H) := by rw [hAH, ContinuousLinearMap.comp_id]
    _ = (d.comp A).comp H := rfl
    _ = _ := by rw [hchain]

variable [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

private local instance adaptedTangentNormed (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance adaptedTangentSpace (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance adaptedTangentInner (x : M) : InnerProductSpace ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance

/-- The margin of the SAME actual adapted phase, together with the actual
forward-chart norm, produces the original transverse reserve. -/
theorem actual_increment_adapted_phase_frame_reserve
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hforward : ‖(tangentSpaceCastModel 𝓙 (chart (chart.symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓙 chart (chart.symm x))‖^2 ≤ C)
    (hmargin :
      let xi := (tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x))
      ∀ w : SymmetricSquare xi.ker, eta * ‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL F hF (chart.symm x)) xi w‖)
    (t : Tdata) :
    (eta / (C * actualIncrementSortedSymmetricConstant m))^2 * ‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF chart.symm x t‖^2 := by
  have hphase := actual_increment_phaseCovector_eq_chosen_chart psi chart hchart O hO hOt x hx hpsi hadapt
  apply actual_increment_chart_frame_reserve F hF chart hchart x (hOt hx) eta C heta hC hforward
  dsimp only at hmargin ⊢
  rw [← hphase]
  exact hmargin

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_phaseCovector_eq_chosen_chart
#print axioms GlobalEmbedding.Continuation.actual_increment_adapted_phase_frame_reserve
