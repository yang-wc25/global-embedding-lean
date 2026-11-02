import Smoothing.Round4ActualPhaseMarginTransport
import Probes.Round4UniformTemplateBlock

/-! The SAME genuine template chart supplies the coordinate restriction
reserve used here. Its frozen covector generates the actual chart-linear
physical phase, and the output is the original intrinsic true-form margin.
Only the genuine host inverse-differential norm conversion is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateIntrinsicRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateIntrinsicSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateIntrinsicTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateIntrinsicTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance templateIntrinsicTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance templateIntrinsicTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance templateIntrinsicTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

theorem round4_actual_uniform_template_intrinsic_margin
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ)
    (x : X) (ell : ℝ)
    (i : (actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart hdim R mu c H hmu hc
      (fun z => (round4ActualPhaseOperatorInChart F e z,A z)) O x ell i a)
    (C : ℝ) (hC : 0 < C)
    (hInverse : ∀ z, ∀ hz : z ∈ block.chart.source,
      ‖(actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2
        (hcoord z (block.source_domain hz))).toContinuousLinearMap‖^2 ≤ C) :
    let provider := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let xi := (provider.template i).covectors a
    let psi := fun p y => xi (e p y)
    ∀ z ∈ block.chart.source,
      let dpsi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
      ∀ w : SymmetricSquare dpsi.ker, (provider.restrictionReserve/C)*‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) dpsi w‖ := by
  intro provider xi psi z hz
  have hzO : z ∈ O := block.source_domain hz
  have hPhase : ∀ y ∈ O, psi y.1 ((e y.1).symm y.2) = xi y.2 := by
    intro y hy
    change xi (e y.1 ((e y.1).symm y.2)) = xi y.2
    rw [(e y.1).right_inv (hcoord y hy)]
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2) :=
    xi.differentiableAt.mdifferentiableAt.comp _
      ((actual_increment_maximal_chart_mdifferentiable (e z.1) (he z.1)).mdifferentiableAt
        ((e z.1).map_target (hcoord z hzO)))
  exact round4_actual_coordinate_margin_to_phase F hF e he O hO hcoord hJoint psi xi
    hPhase z hzO hpsi provider.restrictionReserve C provider.restrictionReserve_pos.le hC
    (hInverse z hz) (block.kernel_reserve z hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_intrinsic_margin
