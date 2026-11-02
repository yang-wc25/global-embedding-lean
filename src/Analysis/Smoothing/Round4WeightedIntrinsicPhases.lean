import Smoothing.Round4OriginalTensorReconstruction
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

theorem round4_actual_weighted_intrinsic_phases
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hOcoord : ∀ z ∈ O, z.2 ∈ host.target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (rho : ℝ) (s : Finset X)
    (pick : s → (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (charts : ∀ z : s, ∀ a, Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun y => (round4ActualPhaseOperatorInChart F (fun _ => host) y,A y)) O z.val rho (pick z) a)
    (label : s × EdgePair (Module.finrank ℝ D+1) → ℕ) (hLabel : Function.Injective label)
    (chi : s → X → ℝ)
    (hSupport : ∀ (z : s) a, tsupport (chi z) ⊆ (charts z a).chart.source) :
    let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let xi := round4WeightedTemplateCovector C pick label
    (∀ (z : s) a y, y ∈ (charts z a).chart.source →
      GoodCovector (F y.1) (hF y.1) (host.symm y.2)
        (round4HostPhaseCovector host (xi z a) (host.symm y.2))) ∧
    (∀ (z : s) a y, y ∈ (charts z a).chart.source →
      GoodCovector (F y.1) (hF y.1) (host.symm y.2)
        ((2 : ℝ) • round4HostPhaseCovector host (xi z a) (host.symm y.2))) ∧
    (∀ y (za zb : s × EdgePair (Module.finrank ℝ D+1)),
      y ∈ tsupport (chi za.1) → y ∈ tsupport (chi zb.1) → za ≠ zb →
      GoodCovector (F y.1) (hF y.1) (host.symm y.2)
        (round4HostPhaseCovector host (xi za.1 za.2) (host.symm y.2) +
          round4HostPhaseCovector host (xi zb.1 zb.2) (host.symm y.2)) ∧
      GoodCovector (F y.1) (hF y.1) (host.symm y.2)
        (round4HostPhaseCovector host (xi za.1 za.2) (host.symm y.2) -
          round4HostPhaseCovector host (xi zb.1 zb.2) (host.symm y.2))) := by
  classical
  intro C xi
  have hpow (z : s) a : (round4TemplateHierarchy C)^label (z,a) ≠ 0 :=
    pow_ne_zero _ (zero_lt_one.trans (round4TemplateHierarchy_gt_one C)).ne'
  have hNative (z : s) a y (hy : y ∈ (charts z a).chart.source) :
      LinearSecondFormGoodCovector (round4ActualPhaseOperatorInChart F (fun _ => host) y).toLinearMap
        (xi z a).toLinearMap := by
    exact (linearSecondFormGoodCovector_continuous_smul_iff _ _ _ (hpow z a)).mpr
      ((C.template (pick z)).operator_control _ ((charts z a).operator_domain y hy) a).1
  let a0 : EdgePair (Module.finrank ℝ D+1) :=
    ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ) < 1; omega⟩
  have hInteractions := round4_weighted_template_interactions_on_support C pick label chi
    (round4ActualPhaseOperatorInChart F (fun _ => host))
    (fun z y hy => (charts z a0).operator_domain y (hSupport z a0 hy))
    (fun y za zb hza hzb hne heq => hne (hLabel heq))
  refine ⟨?_,?_,?_⟩
  · intro z a y hy
    exact round4_actual_host_linear_phase_good F hF host hhost O hO hJoint y
      ((charts z a).source_domain hy) (hOcoord y ((charts z a).source_domain hy)) (xi z a)
      (hNative z a y hy)
  · intro z a y hy
    have hyO := (charts z a).source_domain hy
    rw [round4HostPhaseCovector_eq host hhost (xi z a) y.2 (hOcoord y hyO)]
    exact round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
      O hO hJoint y hyO (hOcoord y hyO) ((2 : ℝ) • xi z a)
      ((linearSecondFormGoodCovector_continuous_smul_iff _ _ (2 : ℝ) (by norm_num)).mpr (hNative z a y hy))
  · intro y za zb hza hzb hne
    have hyO := (charts za.1 za.2).source_domain (hSupport za.1 za.2 hza)
    have hycoord := hOcoord y hyO
    rw [round4HostPhaseCovector_eq host hhost _ y.2 hycoord,
      round4HostPhaseCovector_eq host hhost _ y.2 hycoord]
    have hGood := hInteractions.2.2 y za zb hza hzb hne
    exact ⟨round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
      O hO hJoint y hyO hycoord (xi za.1 za.2+xi zb.1 zb.2) hGood.1,
      round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
      O hO hJoint y hyO hycoord (xi za.1 za.2-xi zb.1 zb.2) hGood.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_weighted_intrinsic_phases
