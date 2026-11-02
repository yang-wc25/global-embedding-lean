import Probes.Round4ActualTemplateField
import Probes.Round4UniformTemplateLinearPhase
import Probes.Round4LinearPhaseSameChart

/-!
A local piece of the uniform preparation, containing the actual field,
one frozen positive dictionary, and genuine phase charts at every order.
The radius and all numerical chart costs are chosen from the allowed class
and a low derivative bound. The operator/tensor reserves hold throughout
each chart source, not merely at the chosen center.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function Manifold
open scoped TensorProduct Topology ContDiff NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance blockRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance blockSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance blockTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  inferInstance
private local instance blockTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  inferInstance

structure Round4UniformTemplateChart
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
    (O : Set X) (x : X) (ell : ℝ)
    (i : (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D + 1)) where
  chart : OpenPartialHomeomorph X X
  source_ball : chart.source = ball x (actualEuclideanPhaseRadius
    (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
    (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound ell)
  source_convex : Convex ℝ chart.source
  target_convex : Convex ℝ chart.target
  inner : ball x (actualEuclideanPhaseRadius
    (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
    (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound ell) ⊆ chart.source
  outer : chart.source ⊆ ball x ell
  target_inner : closedBall (chart x)
    (actualEuclideanPhaseRadius
      (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
      (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound ell /
      (4*actualPhaseInverseConstant
        (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
        (2*(actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound)))
    ⊆ chart.target
  source_domain : chart.source ⊆ O
  operator_domain : ∀ z ∈ chart.source,
    (f z).1 ∈ (((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).operatorDomain)
  tensor_domain : ∀ z ∈ chart.source,
    (f z).2 ∈ (((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).tensorDomain)
  smooth : ContDiffOn ℝ ∞ chart chart.source
  inverse_smooth : ContDiffOn ℝ ∞ chart.symm chart.target
  parameter_forward : ∀ z ∈ chart.source, (chart z).1 = z.1
  phase_forward : ∀ z ∈ chart.source, (chart z).2 0 =
    ((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).covectors a z.2
  parameter_inverse : ∀ z ∈ chart.target, (chart.symm z).1 = z.1
  phase_inverse : ∀ z ∈ chart.target,
    ((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).covectors a
      (chart.symm z).2 = z.2 0
  good : ∀ z ∈ chart.source,
    LinearSecondFormGoodCovector (f z).1.toLinearMap
      (((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).covectors a).toLinearMap
  kernel_reserve : ∀ z ∈ chart.source, ∀ w,
    (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).restrictionReserve * ‖w‖ ≤
      ‖covectorRestriction (f z).1
        (((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).covectors a) w‖
  coefficient_reserve : ∀ z ∈ chart.source,
    (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).coefficientReserve ≤
      ((actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).template i).coefficients (f z).2 a
  forward_value : ∀ z ∈ chart.source, ‖chart z‖ ≤
    2*(1+2*(actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound)*‖z‖
  forward_bound : ∀ z ∈ chart.source, ‖fderiv ℝ chart z‖ ≤
    2*(1+2*(actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound)
  forward_higher_zero : ∀ k, 1 ≤ k → ∀ z ∈ chart.source,
    iteratedFDeriv ℝ (k+1) chart z = 0
  inverse_bound : ∀ z ∈ chart.target, ‖fderiv ℝ chart.symm z‖ ≤
    2*actualPhaseInverseConstant
      (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
      (2*(actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound)
  inverse_higher_zero : ∀ k, 1 ≤ k → ∀ z ∈ chart.target,
    iteratedFDeriv ℝ (k+1) chart.symm z = 0
  inverse_jets : ∀ (j : ℕ) (weight : ℝ), 0 < weight →
    ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ chart.target,
      weight^(k-1)*‖iteratedFDeriv ℝ k chart.symm z‖ ≤ actualEuclideanPhaseInverseJetCost
        (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
        (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).covectorBound 0 j

theorem round4_uniform_template_block
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
    (O : Set X) (L : ℝ≥0) (hf : LipschitzOnWith L f O)
    (x : X) (hx : x ∈ O) (hfx : f x ∈ actualAllowedPhaseTensorData D V R mu c H)
    (ell : ℝ) (hell : 0 < ell) (hball : ball x ell ⊆ O)
    (hellr : ell ≤ round4UniformTemplateRadius D V hdim R mu c H hmu hc / ((L : ℝ)+1)) :
    ∃ i : (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).indices,
      ∀ a, Nonempty (Round4UniformTemplateChart hdim R mu c H hmu hc f O x ell i a) := by
  let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
  obtain ⟨_, i, hi⟩ := round4_uniform_template_on_lipschitz_neighborhood D V
    hdim R mu c H hmu hc f O L hf x hx hfx
  refine ⟨i, ?_⟩
  intro a
  have heta := round4UniformTemplateCovectorLower_spec D V hdim R mu c H hmu hc
  obtain ⟨b, hsource, houter, htargetConvex, hs, hsi, hfwd, hinv, htarget, hvalue, hfirst, hhigh,
      hifirst, hihigh, hjets⟩ :=
    round4_actual_linear_phase_same_chart
      (round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc)
      C.covectorBound heta.1 C.covectorBound_pos.le ((C.template i).covectors a)
      (heta.2 i a) ((C.bounds i).2.2.2.2 a) x ell hell
  have hdom (z : X) (hz : z ∈ b.source) :
      (f z).1 ∈ (C.template i).operatorDomain ∧ (f z).2 ∈ (C.template i).tensorDomain :=
    hi z ⟨hball (houter hz), ball_subset_ball hellr (houter hz)⟩
  refine ⟨{
    chart := b
    source_ball := hsource
    source_convex := by rw [hsource]; exact convex_ball _ _
    target_convex := htargetConvex
    inner := by rw [hsource]
    outer := houter
    target_inner := htarget
    source_domain := fun _ hz => hball (houter hz)
    operator_domain := fun z hz => (hdom z hz).1
    tensor_domain := fun z hz => (hdom z hz).2
    smooth := hs
    inverse_smooth := hsi
    parameter_forward := fun z hz => (hfwd z hz).1
    phase_forward := fun z hz => (hfwd z hz).2
    parameter_inverse := fun z hz => (hinv z hz).1
    phase_inverse := fun z hz => (hinv z hz).2
    good := fun z hz => ((C.template i).operator_control (f z).1 (hdom z hz).1 a).1
    kernel_reserve := ?_
    coefficient_reserve := ?_
    forward_value := hvalue
    forward_bound := hfirst
    forward_higher_zero := hhigh
    inverse_bound := hifirst
    inverse_higher_zero := hihigh
    inverse_jets := hjets }⟩
  · intro z hz w
    exact (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg w)).trans
      (((C.template i).operator_control (f z).1 (hdom z hz).1 a).2.1 w)
  · intro z hz
    exact (C.bounds i).2.1.trans
      ((C.template i).coefficient_control (f z).2 (hdom z hz).2 a)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- Instantiation with the actual map's normal second form. Its operator
reserves, the same chart's target ball, and all chart derivative bounds are
derived from these low inputs. A free normal is constructed separately. -/
theorem round4_actual_uniform_template_block
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu cT H : ℝ) (hmu : 0 < mu) (hcT : 0 < cT)
    (c MA MH : ℝ) (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) (MT : ℝ≥0)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓘(ℝ,D) ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ)
    (hA : ∀ z ∈ O, DifferentiableAt ℝ A z)
    (hAT : ∀ z ∈ O, ‖fderiv ℝ A z‖₊ ≤ MT)
    (x : X) (hx : x ∈ O)
    (hfx : (round4ActualPhaseOperatorInChart F e x, A x) ∈
      actualAllowedPhaseTensorData D V R mu cT H)
    (ell : ℝ) (hell : 0 < ell) (hball : ball x ell ⊆ O)
    (hellr : ell ≤ round4UniformTemplateRadius D V hdim R mu cT H hmu hcT /
      ((round4ActualTemplateFieldLipschitz m N c MA MH hc hMA hMH MT : ℝ)+1)) :
    ∃ i : (actualUniformPhaseTemplateProvider D V hdim R mu cT H hmu hcT).indices,
      ∀ a, Nonempty (Round4UniformTemplateChart hdim R mu cT H hmu hcT
        (fun z => (round4ActualPhaseOperatorInChart F e z, A z)) O x ell i a) :=
  round4_uniform_template_block hdim R mu cT H hmu hcT _ O
    (round4ActualTemplateFieldLipschitz m N c MA MH hc hMA hMH MT)
    (round4_actual_template_field_lipschitz F hF e he O hO hConv hcoord hJoint
      c MA MH hc hMA hMH hreserve hAj hHj A MT hA hAT) x hx hfx ell hell hball hellr

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_block
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_block
