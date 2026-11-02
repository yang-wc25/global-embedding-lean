import NormalPolar.IdentificationTransportGeometry
import Round2.ProbeBridgeSecondForm
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Native derivatives of the actual change of normal identification

The derivative of the gauge is calculated from the two actual ambient Qops.
For the identified true form the full product rule is retained, including
the gauge derivative on the current old-identified form.
-/

noncomputable section
open Manifold Filter Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section Operators
variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Native product and adjoint differentiation. Neither the product
derivative nor an adjoint-derivative formula is a premise. -/
theorem fderiv_comp_adjoint_apply
    (A B : P → V →L[ℝ] V) (u d : P)
    (hA : DifferentiableAt ℝ A u) (hB : DifferentiableAt ℝ B u) :
    fderiv ℝ (fun v ↦ (A v).comp (B v).adjoint) u d =
      (A u).comp (fderiv ℝ B u d).adjoint +
        (fderiv ℝ A u d).comp (B u).adjoint := by
  let adj : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj := adj.hasFDerivAt.comp u hB.hasFDerivAt
  have hprod := hA.hasFDerivAt.clm_comp hadj
  change HasFDerivAt (fun v ↦ (A v).comp (B v).adjoint) _ u at hprod
  rw [hprod.fderiv]
  rfl

theorem differentiableAt_comp_adjoint
    (A B : P → V →L[ℝ] V) (u : P)
    (hA : DifferentiableAt ℝ A u) (hB : DifferentiableAt ℝ B u) :
    DifferentiableAt ℝ (fun v ↦ (A v).comp (B v).adjoint) u := by
  let adj : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  exact hA.clm_comp (adj.differentiableAt.comp u hB)

/-- For contraction factors the gauge response is bounded by the sum of
their genuine responses. This applies to actual normal identifications. -/
theorem norm_fderiv_comp_adjoint_apply_le
    (A B : P → V →L[ℝ] V) (u d : P)
    (hA : DifferentiableAt ℝ A u) (hB : DifferentiableAt ℝ B u)
    (hAnorm : ‖A u‖ ≤ 1) (hBnorm : ‖B u‖ ≤ 1) :
    ‖fderiv ℝ (fun v ↦ (A v).comp (B v).adjoint) u d‖ ≤
      ‖fderiv ℝ A u d‖ + ‖fderiv ℝ B u d‖ := by
  rw [fderiv_comp_adjoint_apply A B u d hA hB]
  calc
    _ ≤ ‖(A u).comp (fderiv ℝ B u d).adjoint‖ +
        ‖(fderiv ℝ A u d).comp (B u).adjoint‖ := norm_add_le _ _
    _ ≤ ‖A u‖ * ‖fderiv ℝ B u d‖ + ‖fderiv ℝ A u d‖ * ‖B u‖ := by
      simpa only [LinearIsometryEquiv.norm_map] using
        add_le_add (ContinuousLinearMap.opNorm_comp_le (A u) (fderiv ℝ B u d).adjoint)
          (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ A u d) (B u).adjoint)
    _ ≤ 1 * ‖fderiv ℝ B u d‖ + ‖fderiv ℝ A u d‖ * 1 :=
      add_le_add (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hBnorm (norm_nonneg _))
    _ = _ := by ring

end Operators

variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem differentiableAt_normalIdentificationGaugeOperator
    (F₀ : M → V) (F : P → M → V)
    (Qold Qnew : ∀ u z, normalSpace (I := IM) (F u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (u : P) (z : M)
    (hold : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u)
    (hnew : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u) :
    DifferentiableAt ℝ
      (fun v ↦ normalIdentificationGaugeOperator F₀ (F v) (Qold v) (Qnew v) z) u := by
  simp_rw [normalIdentificationGaugeOperator_eq_comp_adjoint]
  exact differentiableAt_comp_adjoint _ _ u hnew hold

/-- The response of the actual gauge is derived from the two actual Q
responses on the same map; it is not an independent budget assumption. -/
theorem norm_fderiv_normalIdentificationGaugeOperator_apply_le
    (F₀ : M → V) (F : P → M → V)
    (Qold Qnew : ∀ u z, normalSpace (I := IM) (F u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (u d : P) (z : M)
    (hold : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u)
    (hnew : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u) :
    ‖fderiv ℝ
      (fun v ↦ normalIdentificationGaugeOperator F₀ (F v) (Qold v) (Qnew v) z) u d‖ ≤
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u d‖ +
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u d‖ := by
  simp_rw [normalIdentificationGaugeOperator_eq_comp_adjoint]
  exact norm_fderiv_comp_adjoint_apply_le _ _ u d hnew hold
    (normalIdentificationOperator_norm_le_one F₀ (F u) (Qnew u) z)
    (normalIdentificationOperator_norm_le_one F₀ (F u) (Qold u) z)

/-- The exact native product rule for the actual framed identified true
form when the same map is given a different normal identification. -/
theorem fderiv_framed_identifiedTrueSecondForm_transport
    (F₀ : M → V) (F : P → M → V)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (Qold Qnew : ∀ u z, normalSpace (I := IM) (F u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (u d : P) (z : M) (frame : E →L[ℝ] E)
    (hold : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u)
    (hnew : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u)
    (hform : DifferentiableAt ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)) u) :
    fderiv ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qnew v) z)) u d =
      (normalIdentificationGaugeOperator F₀ (F u) (Qold u) (Qnew u) z).comp
        (fderiv ℝ (fun v ↦ probeTensorInFrame frame
          (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)) u d) +
      (fderiv ℝ
        (fun v ↦ normalIdentificationGaugeOperator F₀ (F v) (Qold v) (Qnew v) z) u d).comp
        (probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ (F u) (hF u) (Qold u) z)) := by
  have hg := differentiableAt_normalIdentificationGaugeOperator F₀ F Qold Qnew u z hold hnew
  have heq : (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qnew v) z)) =
      fun v ↦ (normalIdentificationGaugeOperator F₀ (F v) (Qold v) (Qnew v) z).comp
        (probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)) := by
    funext v
    exact framed_identifiedTrueSecondForm_eq_gauge_comp F₀ (F v) (hF v) (Qold v) (Qnew v) z frame
  rw [heq, fderiv_clm_comp hg hform]
  rfl

/-- Full response transport for the same actual map. The old response
error, gauge alignment error and both true Q derivatives are retained. -/
theorem norm_fderiv_framed_identifiedTrueSecondForm_transport_le
    (F₀ : M → V) (F : P → M → V)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (Qold Qnew : ∀ u z, normalSpace (I := IM) (F u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (u d : P) (z : M) (frame : E →L[ℝ] E)
    (L : SymmetricSquare E →L[ℝ] V)
    (hL : (normalSpace (I := IM) F₀ z).starProjection.comp L = L)
    (hold : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u)
    (hnew : DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u)
    (hform : DifferentiableAt ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)) u) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame frame
        (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qnew v) z)) u d - L‖ ≤
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame frame
        (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)) u d - L‖ +
      ‖normalIdentificationOperator (n := n) F₀ (F u) (Qnew u) z -
        normalIdentificationOperator (n := n) F₀ (F u) (Qold u) z‖ * ‖L‖ +
      (‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qnew v) z) u d‖ +
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Qold v) z) u d‖) *
        ‖probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ (F u) (hF u) (Qold u) z)‖ := by
  let G := fun v ↦ normalIdentificationGaugeOperator F₀ (F v) (Qold v) (Qnew v) z
  let B := fun v ↦ probeTensorInFrame frame
    (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qold v) z)
  have hg := differentiableAt_normalIdentificationGaugeOperator F₀ F Qold Qnew u z hold hnew
  have h := norm_parameter_identified_operator_response_sub_le G B
    (normalSpace (I := IM) F₀ z).starProjection L u d hg hform
    (normalIdentificationGaugeOperator_norm_le_one F₀ (F u) (Qold u) (Qnew u) z) hL
  have heq : (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Qnew v) z)) =
      fun v ↦ (G v).comp (B v) := by
    funext v
    exact framed_identifiedTrueSecondForm_eq_gauge_comp F₀ (F v) (hF v) (Qold v) (Qnew v) z frame
  rw [heq]
  apply h.trans
  exact add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (normalIdentificationGaugeOperator_sub_projection_le F₀ (F u) (Qold u) (Qnew u) z)
      (norm_nonneg L)))
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_normalIdentificationGaugeOperator_apply_le F₀ F Qold Qnew u d z hold hnew)
      (norm_nonneg (B u)))

end GlobalEmbedding.NormalPolar
