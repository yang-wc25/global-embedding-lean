import Smoothing.Round4ActualNormalCarrier
import Probes.ActualQuantitativeAdaptedRefinement

/-! One actual normal serves the ENTIRE support ball of the refinement
cutoff. The construction radius obeys a numerical cap chosen before the
fields. The same chart, slices, coordinate, and high-order normal estimates
are retained for later finite-family assembly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance templateNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateNormalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance templateNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

theorem round4_actual_template_normal_carrier
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (W : Set X) (hW : IsOpen W) (hWcoord : ∀ z ∈ W, z.2 ∈ host.target)
    (hHostJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (center : X) (ell0 : ℝ) (hell0 : 0 < ell0)
    (index : (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun z => (round4ActualPhaseOperatorInChart F (fun _ => host) z,A z)) W center ell0 index a)
    (c0 K : ℝ) (hc0 : 0 < c0) (hK : 0 ≤ K)
    (hFirst0 : ∀ z ∈ W, ∀ v : D,
      c0*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ host.symm) z.2 v‖^2)
    (hC3 : ∀ k ≤ 3, ∀ z ∈ W, ‖iteratedFDeriv ℝ k
      (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ K)

    (hdim : (m+1)*(m+2)/2 < N)
    (hcap :
      let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
      let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
      let B := 2*(1+2*provider.covectorBound)
      let I := 2*actualPhaseInverseConstant eta (2*provider.covectorBound)
      ell0 ≤ actualPhaseRefinementFactor eta provider.covectorBound *
        round4NativeNormalRadius m N c0 B I provider.restrictionReserve K/(4*B)) :
    let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
    let B := 2*(1+2*provider.covectorBound)
    let I := 2*actualPhaseInverseConstant eta (2*provider.covectorBound)
    let rhoN := round4NativeNormalRadius m N c0 B I provider.restrictionReserve K
    let cF := c0/B^2
    let cT := (provider.restrictionReserve/(B^2*actualIncrementSortedSymmetricConstant m))^2
    let r := ell0/actualPhaseRefinementFactor eta provider.covectorBound
    0 < rhoN ∧
    ∃ data : Round4ActualNormalCarrier F hF host block.chart
      (fun z => (provider.template index).covectors a (host z.2)) center rhoN cF cT,
      closedBall center (2*r) ⊆ round4NormalCutoffCarrier block.chart center rhoN := by
  intro provider eta B I rhoN cF cT r
  have heta : 0 < eta := (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1
  have hfactor : 0 < actualPhaseRefinementFactor eta provider.covectorBound :=
    actualPhaseRefinementFactor_pos heta provider.covectorBound_pos.le
  have hr : 0 < r := div_pos hell0 hfactor
  have hB : 0 < B := by have := provider.covectorBound_pos; dsimp [B]; positivity
  have hrad : 4*r = actualEuclideanPhaseRadius eta provider.covectorBound ell0 :=
    actualPhaseRefinementFactor_radius eta provider.covectorBound ell0
  have hcenter : center ∈ block.chart.source := block.inner (by rw [← hrad]; exact mem_ball_self (by positivity))
  have hSource : closedBall center (2*r) ⊆ block.chart.source := by
    apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
    rw [hrad]
    exact block.inner
  obtain ⟨e,hdata,hJoint,hNormal⟩ := round4_actual_uniform_template_native_c3_normal_factory
    templateDim R mu c H hmu hc F hF host hhost W hW hWcoord hHostJoint A center ell0 index a block
    c0 K hc0 hK hFirst0 hC3
  obtain ⟨hrho,i,hSmooth,hLegal,hJets⟩ := hNormal block.chart.target block.chart.open_target
    block.target_convex Subset.rfl hdim (block.chart center) (block.chart.map_source hcenter)
  let data : Round4ActualNormalCarrier F hF host block.chart
      (fun z => (provider.template index).covectors a (host z.2)) center rhoN cF cT := {
    slices := e
    slices_data := hdata
    coordinate := i
    normal_smooth := hSmooth
    normal_legal := hLegal
    normal_jets := hJets }
  refine ⟨hrho,data,?_⟩
  apply round4_actual_closedBall_in_normal_carrier block.chart block.smooth block.source_convex
    B hB.le block.forward_bound center hcenter r rhoN hSource
  exact round4_normal_refinement_cap hfactor hrho hB hcap

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_template_normal_carrier
