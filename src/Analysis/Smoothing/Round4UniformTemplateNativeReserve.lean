import Smoothing.Round4NativeFrameReserve
import Probes.Round4UniformTemplateBlock

/-! The same actual template chart supplies the original transverse-frame
reserve directly in native Euclidean coordinates. The fixed template
margin and the SAME chart's forward derivative bound are sufficient.
No Riemannian host-inverse bound or intrinsic chosen-margin input is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativeTemplateRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativeTemplateSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance nativeTemplateTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance nativeTemplateTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4_actual_uniform_template_native_frame_reserve
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (W : Set X) (hW : IsOpen W)
    (hHostJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (T : X → D →L[ℝ] D →L[ℝ] ℝ) (center : X) (ell0 : ℝ)
    (index : (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun z => (round4ActualPhaseOperatorInChart F (fun _ => host) z,T z)) W center ell0 index a)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host block.chart
      (fun z => ((actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).template index).covectors a (host z.2)) e)
    (z : X) (hz : z ∈ block.chart.target) (t : Tdata) :
    let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let C := (2*(1+2*provider.covectorBound))^2
    (provider.restrictionReserve/(C*actualIncrementSortedSymmetricConstant m))^2*‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t‖^2 := by
  intro provider C
  let b := block.chart
  let xi := (provider.template index).covectors a
  have hGeom := actual_host_slice_geometry_inputs host hhost b (fun z => xi (host z.2)) e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  obtain ⟨A,hA,hAi,hxi,hAn⟩ := round4_actual_native_spatial_equiv b block.smooth block.inverse_smooth
    block.parameter_forward block.parameter_inverse xi block.phase_forward
    (2*(1+2*provider.covectorBound)) block.forward_bound z hz
  have hJ : actualJointSpatialJacobian (actualSourceChartTransition (fun _ => host) e) z =
      actualJointSpatialJacobian b.symm z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(b.open_target.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
      with x hx
    exact congrArg Prod.snd (hback hx)
  have hQ := actual_normal_hessian_true_chart_transition F hF (fun _ => host) e (fun _ => hhost)
    b.target W b.open_target hW hHostJoint hGeom.2.2.2.2.1
    (fun y hy => block.source_domain (hGeom.2.2.2.2.2.2.1 hy)) hGeom.2.2.2.1 z hz
  rw [hback hz,hJ,← hA] at hQ
  have hBpos : 0 < 2*(1+2*provider.covectorBound) := by
    have := provider.covectorBound_pos
    positivity
  have hC : 0 < C := sq_pos_of_pos hBpos
  exact round4_actual_native_frame_reserve F hF (fun _ => host) e he W hW hHostJoint
    (b.symm z) (block.source_domain (b.map_target hz)) z (hGeom.2.2.2.1 z hz).1
    A hQ xi hxi provider.restrictionReserve C provider.restrictionReserve_pos.le hC
    ((sq_le_sq₀ (norm_nonneg _) hBpos.le).mpr hAn)
    (block.kernel_reserve (b.symm z) (b.map_target hz)) t

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_native_frame_reserve
