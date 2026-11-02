import Smoothing.Round4TemplateNormalCarrier
import Smoothing.Round4NormalPhaseScaling
import Probes.Round4UniformWeightedTemplateAssembly

/-! The existing finite refinement receives actual unit normals on the whole
support of each cutoff. No centers, labels, charts or cutoffs are changed.
The same normal is free for the actual hierarchical weighted phase. -/

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
variable {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep] {m N : ℕ}
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

theorem round4_actual_weighted_template_normal_family
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hOcoord : ∀ z ∈ O, z.2 ∈ host.target)
    (hHostJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (rho : ℝ) (hrho : 0 < rho)
    (s : Finset X)
    (pick : s → (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (charts : ∀ z : s, ∀ a, Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun y => (round4ActualPhaseOperatorInChart F (fun _ => host) y,A y)) O z.val rho (pick z) a)
    (label : s × EdgePair (Module.finrank ℝ D+1) → ℕ)
    (c0 K : ℝ) (hc0 : 0 < c0) (hK : 0 ≤ K)
    (hFirst0 : ∀ z ∈ O, ∀ v : D,
      c0*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ host.symm) z.2 v‖^2)
    (hC3 : ∀ k ≤ 3, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ K)
    (hdim : (m+1)*(m+2)/2 < N)
    (hcap :
      let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
      let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
      let B := 2*(1+2*C.covectorBound)
      let I := 2*actualPhaseInverseConstant eta (2*C.covectorBound)
      rho ≤ actualPhaseRefinementFactor eta C.covectorBound *
        round4NativeNormalRadius m N c0 B I C.restrictionReserve K/(4*B)) :
    let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
    let B := 2*(1+2*C.covectorBound)
    let I := 2*actualPhaseInverseConstant eta (2*C.covectorBound)
    let rhoN := round4NativeNormalRadius m N c0 B I C.restrictionReserve K
    let cF := c0/B^2
    let cT := (C.restrictionReserve/(B^2*actualIncrementSortedSymmetricConstant m))^2
    let r := rho/actualPhaseRefinementFactor eta C.covectorBound
    let chi := round4RefinementSquareCutoff X s r
    ∃ data : ∀ (z : s) a, Round4ActualNormalCarrier F hF host (charts z a).chart
      (fun y => (C.template (pick z)).covectors a (host y.2)) z.val rhoN cF cT,
      (∀ (z : s) a, tsupport (chi z) ⊆
        round4NormalCutoffCarrier (charts z a).chart z.val rhoN) ∧
      (∀ (z : s) a, ContDiffOn ℝ ∞
        (round4ActualNormalCarrierHostField F hF host (charts z a).chart
          (fun y => (C.template (pick z)).covectors a (host y.2)) z.val rhoN cF cT (data z a))
        (round4NormalCutoffCarrier (charts z a).chart z.val rhoN)) ∧
      (∀ (z : s) a y, y ∈ round4NormalCutoffCarrier (charts z a).chart z.val rhoN →
        Round4PhaseNormalAt F hF
          (fun p => round4WeightedTemplateCovector C pick label z a (host p.2))
          (y.1,host.symm y.2)
          (round4ActualNormalCarrierHostField F hF host (charts z a).chart
            (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a) y)) := by
  classical
  intro C eta B I rhoN cF cT r chi
  have hr : 0 < r := div_pos hrho (actualPhaseRefinementFactor_pos
    (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1 C.covectorBound_pos.le)
  have hdata (z : s) (a : EdgePair (Module.finrank ℝ D+1)) :=
    (round4_actual_template_normal_carrier templateDim R mu c H hmu hc F hF host hhost
      O hO hOcoord hHostJoint A z.val rho hrho (pick z) a (charts z a)
      c0 K hc0 hK hFirst0 hC3 hdim hcap).2
  choose data hsupport using hdata
  refine ⟨data,?_,?_,?_⟩
  · intro z a
    apply (tensorLocalNormalizedCutoff_tsupport_subset
      (fun q : s => actualRefinementBump X r q.val) z).trans
    rw [actualRefinementBump_tsupport X r hr z.val]
    exact hsupport z a
  · intro z a
    exact round4_actual_normal_carrier_host_smooth F hF host (charts z a).chart
      (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT
      (data z a) (charts z a).smooth
  · intro z a y hy
    have hbase := round4_actual_normal_carrier_host_legal F hF host (charts z a).chart
      (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a) y hy
    have hsource : host.symm y.2 ∈ host.source :=
      host.map_target (hOcoord y ((charts z a).source_domain hy.1))
    have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
        (fun x => (C.template (pick z)).covectors a (host x)) (host.symm y.2) :=
      ((C.template (pick z)).covectors a).differentiableAt.mdifferentiableAt.comp _
        ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt hsource)
    have hscale := round4_phase_normal_const_smul F hF
      (fun p => (C.template (pick z)).covectors a (host p.2)) (y.1,host.symm y.2) _ hpsi
      ((round4TemplateHierarchy C)^label (z,a))
      (pow_ne_zero _ (zero_lt_one.trans (round4TemplateHierarchy_gt_one C)).ne') hbase
    simpa only [round4WeightedTemplateCovector, smul_apply] using hscale

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_weighted_template_normal_family
