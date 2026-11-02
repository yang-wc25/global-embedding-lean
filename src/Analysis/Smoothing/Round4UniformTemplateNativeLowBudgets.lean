import Smoothing.Round4UniformTemplateNativeNormalFactory
import Probes.ActualAdaptedFirstFrameReserve
import Probes.Round4UniformTemplateBlock

/-! Original host first-frame coercivity and original low map jets supply
all low adapted budgets for the SAME template slices. The forward and
inverse costs are computed from the template provider, before these fields. -/

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
private local instance nativeTemplateFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance nativeTemplateFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance nativeTemplateHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeTemplateHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeTemplateTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance nativeTemplateTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4_actual_uniform_template_native_low_budgets
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V)
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
    (c0 K : ℝ) (hc0 : 0 < c0) (hK : 0 ≤ K)
    (hFirst : ∀ z ∈ W, ∀ v : D,
      c0*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ host.symm) z.2 v‖^2)
    (hJets : ∀ k ≤ 2, ∀ z ∈ W, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ host.symm) y.2) z‖ ≤ K) :
    let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let B := 2*(1+2*provider.covectorBound)
    let I := 2*actualPhaseInverseConstant
      (round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc)
      (2*provider.covectorBound)
    let K1 := actualFirstFrameTransferCost (fun _ => I) 2*K
    0 < c0/B^2 ∧ 0 ≤ K1 ∧
    (∀ z ∈ block.chart.target, ∀ v : D,
      (c0/B^2)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
    (∀ k ≤ 1, ∀ z ∈ block.chart.target, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ K1) ∧
    (∀ k ≤ 1, ∀ z ∈ block.chart.target, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ K1) := by
  intro provider B I K1
  let b := block.chart
  let xi := (provider.template index).covectors a
  have hGeom := actual_host_slice_geometry_inputs host hhost b (fun z => xi (host z.2)) e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hB : 0 < B := by have := provider.covectorBound_pos; dsimp [B]; positivity
  have hLower := (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1
  have hI : 0 ≤ I := by
    have hh := actualPhaseInverseConstant_one_le hLower
      (show 0 ≤ 2*provider.covectorBound by have := provider.covectorBound_pos; positivity)
    dsimp [I]
    linarith
  have hMap : MapsTo (actualSourceChartTransition (fun _ => host) e) b.target W :=
    fun y hy => block.source_domain (hGeom.2.2.2.2.2.2.1 hy)
  have hRes := actual_adapted_first_frame_reserve_from_original F (fun _ => host) e
    b.target b.source b.open_target b.open_source (hHostJoint.mono block.source_domain)
    hGeom.2.2.2.2.1 hGeom.2.2.2.2.2.1 hGeom.2.2.2.2.2.2.1 hGeom.2.2.2.1
    c0 B hc0 hB (fun z hz => hFirst z (block.source_domain hz)) (by
      intro z hz
      have hg := Filter.eventuallyEq_of_mem (b.open_source.mem_nhds hz)
        (fun y hy => hforward hy)
      rw [hg.fderiv_eq]
      exact block.forward_bound z hz)
  have hP : ∀ k, 1 ≤ k → k ≤ 1+2 → ∀ z ∈ b.target,
      (1:ℝ)^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition (fun _ => host) e) z‖ ≤ I := by
    intro k hk hkj z hz
    rw [hbj k z hz]
    simp only [one_pow, one_mul]
    by_cases h1 : k = 1
    · subst k
      rw [norm_iteratedFDeriv_one]
      exact block.inverse_bound z hz
    · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [block.inverse_higher_zero l (by omega) z hz, norm_zero]
      exact hI
  have hTransfer := actual_first_frame_hessian_transferred_from_original_jets
    (fun _ => I) (fun _ => hI) 1 F (fun _ => host) e b.target W b.open_target hW
    hHostJoint hGeom.2.2.2.2.1 hMap (fun z hz => (hGeom.2.2.2.1 z hz).2)
    1 K zero_lt_one hK (by simpa only [one_pow,one_mul] using hJets) hP
  refine ⟨div_pos hc0 (sq_pos_of_pos hB),
    mul_nonneg (actualFirstFrameTransferCost_nonneg _ (fun _ => hI) 2) hK,hRes,?_,?_⟩
  · intro k hk z hz
    simpa only [one_pow,one_mul] using (hTransfer.2.2.2 k hk z hz).1
  · intro k hk z hz
    simpa only [one_pow,one_mul] using (hTransfer.2.2.2 k hk z hz).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_native_low_budgets
