import Smoothing.Round4UniformTemplateNativeNormal

/-! The same template chart internally constructs actual manifold slices,
then one genuine phase-free normal before all high derivative orders.
Its transverse reserve uses only the native template margin and the same
Euclidean chart norm: no Riemannian Chost or manifold-forward budget. -/

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

theorem round4_actual_uniform_template_native_normal_factory
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
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData host block.chart
        (fun z => ((actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc).template index).covectors a (host z.2)) e ∧
      ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) block.chart.target ∧
    ∀ (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O) (hTarget : O ⊆ block.chart.target)
    (cF MA MH : ℝ) (hcF : 0 < cF) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ O, ∀ w : D,
      cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (hdim : (m+1)*(m+2)/2 < N) (x : X) (hx : x ∈ O),
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
  obtain ⟨e,hdata,hJoint⟩ := round4_actual_uniform_template_host_slices templateDim R mu c H hmu hc
    F hF host hhost W hW hWcoord hHostJoint A center ell0 index a block
  refine ⟨e,hdata,hJoint,?_⟩
  intro O hO hConv hTarget cF MA MH hcF hMA hMH hFirst hAj hHj hdim x hx
  exact round4_actual_uniform_template_native_normal templateDim R mu c H hmu hc
    F hF host hhost W hW hWcoord hHostJoint A center ell0 index a block
    e hdata O hO hConv hTarget (hJoint.mono hTarget)
    cF MA MH hcF hMA hMH hFirst hAj hHj hdim x hx

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_template_native_normal_factory
