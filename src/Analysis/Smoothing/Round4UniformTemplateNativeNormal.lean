import Smoothing.Round4UniformTemplateNativeReserve
import Smoothing.Round4UniformTemplateHostSlices
import Probes.Round4OriginalPhaseNormal
import Probes.ActualIncrementHostGeometryInputs

/-! A true phase-free unit normal from the SAME template kernel reserve,
using only native Euclidean chart conditioning. No Riemannian host norm,
intrinsic chosen-margin budget, or manifold-forward norm is an input. -/

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

theorem round4_actual_uniform_template_native_normal
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
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host block.chart
      (fun z => ((actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).template index).covectors a (host z.2)) e)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O) (hTarget : O ⊆ block.chart.target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (cF MA MH : ℝ) (hcF : 0 < cF) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ O, ∀ w : D,
      cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (hdim : (m+1)*(m+2)/2 < N) (x : X) (hx : x ∈ O) :
    let provider := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let xi := (provider.template index).covectors a
    let psi := fun (_p : Ep) y => xi (host y)
    let eta := provider.restrictionReserve
    let C := (2*(1+2*provider.covectorBound))^2
    let cT := (eta/(C*actualIncrementSortedSymmetricConstant m))^2
    let rho := round4OriginalNormalRadius m N cF cT MA MH
    let S := O ∩ ball x rho
    0 < rho ∧ ∃ i : Fin N,
      let normal := actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1)
      ContDiffOn ℝ ∞ normal S ∧
      (∀ z ∈ S, ∃ nu : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (nu : V) = normal z ∧ ‖nu‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F z.1) (hF z.1) ((e z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) u.val w.val)) : V)
          (nu : V) = 0) ∧
      ∀ (j : ℕ) (ell Aj Hj : ℝ), 0 < ell → 0 ≤ Aj → 0 ≤ Hj →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ Aj) →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ Hj) →
        ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤
          round4OriginalNormalConstant m N j cF cT Aj Hj
            (round4AmbientCoordinateReserve N / 2) 1
            (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num)) := by
  intro provider xi psi eta C cT rho S
  have hGeom := actual_host_slice_geometry_inputs host hhost block.chart (fun z => psi z.1 z.2) e hdata
  have he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M := hdata.2.2.2.2.1
  have hcoord (z : X) (hz : z ∈ O) : z.2 ∈ (e z.1).target := (hGeom.2.2.2.1 z (hTarget hz)).1
  have hSource (z : X) (hz : z ∈ O) : (e z.1).symm z.2 ∈ host.source := (hGeom.2.2.2.1 z (hTarget hz)).2
  have hpsi (z : X) (hz : z ∈ O) : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2) :=
    xi.differentiableAt.mdifferentiableAt.comp _
      ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt (hSource z hz))
  have hadapt (z : X) (hz : z ∈ O) : psi z.1 ((e z.1).symm z.2) = z.2 0 :=
    hGeom.2.2.2.2.2.2.2 z (hTarget hz)
  have hC : 0 < C := sq_pos_of_pos (by
    have := provider.covectorBound_pos
    positivity)
  have hcT : 0 < cT := sq_pos_of_pos
    (div_pos provider.restrictionReserve_pos
      (mul_pos hC (actualIncrementSortedSymmetricConstant_pos m)))
  have hFrame (z : X) (hz : z ∈ O)
      (t : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) :
      cT*‖t‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t‖^2 :=
    round4_actual_uniform_template_native_frame_reserve templateDim R mu c H hmu hc
      F hF host hhost W hW hHostJoint A center ell0 index a block e hdata z (hTarget hz) t
  obtain ⟨hrho,i,hsmooth,hnormal,hjets⟩ := round4_actual_original_uniform_normal_before_all_orders
    F hF e he O hO hConv hcoord hJoint cF cT MA MH hcF hcT hMA hMH
    hFirst hFrame hAj hHj hdim x hx
  refine ⟨hrho,i,hsmooth,?_,hjets⟩
  intro z hz
  obtain ⟨nu,heq,hnorm,hbeta⟩ := hnormal z hz
  refine ⟨nu,heq,hnorm,?_⟩
  exact actual_increment_phase_free_of_transverse_kernel (F z.1) (hF z.1) (psi z.1)
    (e z.1) (he z.1) {y : D | (z.1,y) ∈ O}
    (hO.preimage (continuous_const.prodMk continuous_id))
    (fun y hy => hcoord (z.1,y) hy) z.2 hz.1 (hpsi z hz.1)
    (fun y hy => hadapt (z.1,y) hy) nu hbeta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_native_normal
