import Smoothing.Round4ActualNormalCarrier
import Probes.ActualJointChartTransfer

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

def round4NativeNormalHostConstant (m N j : ℕ) (cF cT B I Kj : ℝ) : ℝ :=
  let K1 := actualFirstFrameTransferCost (fun _ => I) (j+1)*Kj
  actualFastChartTransferPrefix (fun _ => B) j *
    round4OriginalNormalConstant m N j cF cT K1 K1 (round4AmbientCoordinateReserve N/2) 1
      (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num))

theorem round4NativeNormalHostConstant_nonneg (m N j : ℕ) (cF cT B I Kj : ℝ) (hB : 0 ≤ B) :
    0 ≤ round4NativeNormalHostConstant m N j cF cT B I Kj :=
  mul_nonneg (actualFastChartTransferPrefix_nonneg _ (fun _ => hB) j)
    (round4OriginalNormalConstant_nonneg _ _ _ _ _ _ _ _ _ _)

/-- The already chosen actual normal has every host joint derivative
bounded from the same original host map through order j+2. Neither an
adapted high-jet budget nor a normal high-jet budget is assumed. -/
theorem round4_actual_template_normal_host_jets
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (center : X) (rho : ℝ)
    (index : (actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart templateDim R mu c H hmu hc
      (fun z => (round4ActualPhaseOperatorInChart F (fun _ => host) z,A z)) O center rho index a)
    (rhoN cF cT : ℝ)
    (data : Round4ActualNormalCarrier F hF host block.chart
      (fun z => ((actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).template index).covectors a (host z.2))
      center rhoN cF cT)
    (j : ℕ) (Kj : ℝ) (hKj : 0 ≤ Kj)
    (hJets : ∀ k ≤ j+2, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ Kj) :
    let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let B := 2*(1+2*C.covectorBound)
    let I := 2*actualPhaseInverseConstant
      (round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc) (2*C.covectorBound)
    let K1 := actualFirstFrameTransferCost (fun _ => I) (j+1)*Kj
    let Q := round4OriginalNormalConstant m N j cF cT K1 K1
      (round4AmbientCoordinateReserve N/2) 1
      (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num))
    ∀ k ≤ j, ∀ z ∈ round4NormalCutoffCarrier block.chart center rhoN,
      ‖iteratedFDeriv ℝ k
        (round4ActualNormalCarrierHostField F hF host block.chart
          (fun y => (C.template index).covectors a (host y.2)) center rhoN cF cT data) z‖ ≤
        actualFastChartTransferPrefix (fun _ => B) j*Q := by
  intro C B I K1 Q
  let b := block.chart
  let e := data.slices
  let S := b.target ∩ ball (b center) rhoN
  let U := round4NormalCutoffCarrier b center rhoN
  let normal := actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single data.coordinate 1)
  have hdata := data.slices_data
  have hGeom := actual_host_slice_geometry_inputs host hhost b
    (fun z => (C.template index).covectors a (host z.2)) e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hB : 0 ≤ B := by have := C.covectorBound_pos; dsimp [B]; positivity
  have hI : 0 ≤ I := by
    have hLower := (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1
    have hh := actualPhaseInverseConstant_one_le hLower
      (show 0 ≤ 2*C.covectorBound by have := C.covectorBound_pos; positivity)
    dsimp [I]
    linarith
  have hK1 : 0 ≤ K1 := mul_nonneg
    (actualFirstFrameTransferCost_nonneg _ (fun _ => hI) (j+1)) hKj
  have hQ : 0 ≤ Q := round4OriginalNormalConstant_nonneg _ _ _ _ _ _ _ _ _ _
  have hMap : MapsTo (actualSourceChartTransition (fun _ => host) e) b.target O :=
    fun y hy => block.source_domain (hGeom.2.2.2.2.2.2.1 hy)
  have hOriginal : ∀ k ≤ j+1, ∀ z ∈ O, (1:ℝ)^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ host.symm) y.2) z‖ ≤ Kj := by
    intro k hk z hz
    simp only [one_pow,one_mul]
    exact (spatial_first_jet_le hO hJoint hz k).trans (hJets (k+1) (by omega) z hz)
  have hP : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ b.target,
      (1:ℝ)^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition (fun _ => host) e) z‖ ≤ I := by
    intro k hk hkj z hz
    rw [hbj k z hz]
    simp only [one_pow,one_mul]
    by_cases h1 : k = 1
    · subst k
      rw [norm_iteratedFDeriv_one]
      exact block.inverse_bound z hz
    · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [block.inverse_higher_zero l (by omega) z hz,norm_zero]
      exact hI
  have hTransfer := actual_first_frame_hessian_transferred_from_original_jets
    (fun _ => I) (fun _ => hI) j F (fun _ => host) e b.target O b.open_target hO
    hJoint hGeom.2.2.2.2.1 hMap (fun z hz => (hGeom.2.2.2.1 z hz).2)
    1 Kj zero_lt_one hKj hOriginal hP
  have hNormal : ∀ k ≤ j, ∀ z ∈ S, (1:ℝ)^k*‖iteratedFDeriv ℝ k normal z‖ ≤ Q := by
    apply data.normal_jets j 1 K1 K1 zero_lt_one hK1 hK1
    · intro k hk z hz
      exact (hTransfer.2.2.2 k hk z hz.1).1
    · intro k hk z hz
      simpa only [one_pow,one_mul] using (hTransfer.2.2.2 k hk z hz.1).2
  intro k hk z hz
  have hForward : ∀ l, 1 ≤ l → l ≤ k →
      (1:ℝ)^(l-1)*‖iteratedFDeriv ℝ l b z‖ ≤ B := by
    intro l hl hlk
    simp only [one_pow,one_mul]
    by_cases h1 : l = 1
    · subst l
      rw [norm_iteratedFDeriv_one]
      exact block.forward_bound z hz.1
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      rw [block.forward_higher_zero q (by omega) z hz.1,norm_zero]
      exact hB
  have h := actual_fast_joint_chart_transfer (fun _ => B) (fun _ => hB) k b normal U S
    (round4NormalCutoffCarrier_open b center rhoN) (b.open_target.inter isOpen_ball)
    (block.smooth.mono inter_subset_left) data.normal_smooth
    (round4NormalCutoffCarrier_mapsTo b center rhoN) z hz 1 1 Q zero_lt_one le_rfl
    (fun i hi => hNormal i (hi.trans hk) (b z) (round4NormalCutoffCarrier_mapsTo b center rhoN hz)) hForward
  have hHost : ‖iteratedFDeriv ℝ k (normal ∘ b) z‖ ≤
      actualFastChartTransferCost (fun _ => B) k*Q := by
    simpa only [one_pow,one_mul] using h
  exact hHost.trans
    (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix (fun _ => B) (fun _ => hB) hk) hQ)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_template_normal_host_jets
