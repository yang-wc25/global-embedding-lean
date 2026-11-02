import Smoothing.Round4UniformTemplatePhaseNormal

/-! The genuine template chart internally supplies the actual original host
slices and joint smoothness on its full target. The same slices can be
passed directly to the preceding phase-normal theorem; no replacement chart
or independently selected host-slice witness is needed. -/

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

theorem round4_actual_uniform_template_host_slices
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (W : Set X) (hW : IsOpen W) (hWcoord : ∀ z ∈ W, z.2 ∈ host.target)
    (hHostJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (center : X) (ell0 : ℝ)
    (index : (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun z => (round4ActualPhaseOperatorInChart F (fun _ => host) z,A z)) W center ell0 index a)
 :
    let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let xi := (provider.template index).covectors a
    let psi := fun z : Ep × M => xi (host z.2)
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData host block.chart psi e ∧
      ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) block.chart.target := by
  intro provider xi psi
  have hSource : block.chart.source ⊆ (actualOriginalHostJointChart (Ep := Ep) host).target := by
    intro z hz
    exact ⟨mem_univ _,hWcoord z (block.source_domain hz)⟩
  have hPhase (z : X) (hz : z ∈ block.chart.source) :
      (block.chart z).2 0 = psi (z.1,host.symm z.2) := by
    change (block.chart z).2 0 = xi (host (host.symm z.2))
    rw [host.right_inv (hWcoord z (block.source_domain hz))]
    exact block.phase_forward z hz
  obtain ⟨hat,ha,hai,hforw,e,he⟩ := actual_adapted_chart_original_host host hhost psi block.chart
    hSource block.smooth block.inverse_smooth block.parameter_forward hPhase
  have hData : ActualOriginalHostSliceData host block.chart psi e := ⟨hat,ha,hai,hforw,he⟩
  refine ⟨e,hData,?_⟩
  have hCompose := hHostJoint.comp block.inverse_smooth
    (fun z hz => block.source_domain (block.chart.map_target hz))
  apply hCompose.congr
  intro z hz
  have hPair := he.2.2.2.2.2.1 z hz
  have h := congrArg (fun w : Ep × M => F w.1 w.2) hPair
  exact h.symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_host_slices
