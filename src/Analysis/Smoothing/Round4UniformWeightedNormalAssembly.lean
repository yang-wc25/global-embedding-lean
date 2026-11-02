import Smoothing.Round4WeightedTemplateNormalFamily
import Smoothing.Round4UniformNormalRefinementRadius
import Smoothing.Round4TemplateNormalHostJets
import Smoothing.Round4UniformWeightedTemplateProfiles

/-! The existing finite refinement receives actual unit normals on the whole
support of each cutoff. No centers, labels, charts or cutoffs are changed.
The same normal is free for the actual hierarchical weighted phase. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators NNReal
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

def round4UniformNormalPieceBound
    (Ep : Type) [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius buffer c0 K3 : ℝ) (MT : ℝ≥0)
    (hbuffer : 0 < buffer) (hc0 : 0 < c0) (hK3 : 0 ≤ K3) : ℕ :=
  let Lip := round4ActualTemplateFieldLipschitz m N c0 K3 K3 hc0 hK3 hK3 MT
  let rho := round4UniformNormalRefinementRadius (N := N) templateDim R mu c H hmu hc buffer c0 K3 Lip
  let hs := round4UniformNormalRefinementRadius_spec (N := N)
    templateDim R mu c H hmu hc buffer c0 K3 Lip hbuffer hc0 hK3
  Classical.choose (round4_uniform_weighted_template_profiles_before_fields
    (Ep := Ep) templateDim R mu c H hmu hc modelRadius rho hs.1 Lip hs.2.2.1)

def round4UniformNormalCutoffProfile
    (Ep : Type) [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (buffer c0 K3 : ℝ) (MT : ℝ≥0)
    (hbuffer : 0 < buffer) (hc0 : 0 < c0) (hK3 : 0 ≤ K3) (j : ℕ) : ℝ :=
  let Lip := round4ActualTemplateFieldLipschitz m N c0 K3 K3 hc0 hK3 hK3 MT
  let rho := round4UniformNormalRefinementRadius (N := N) templateDim R mu c H hmu hc buffer c0 K3 Lip
  let hs := round4UniformNormalRefinementRadius_spec (N := N)
    templateDim R mu c H hmu hc buffer c0 K3 Lip hbuffer hc0 hK3
  let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
  let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
  let r := rho/actualPhaseRefinementFactor eta C.covectorBound
  round4RefinementSquareProfile (Ep × D) r (div_pos hs.1
    (actualPhaseRefinementFactor_pos
      (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1
      C.covectorBound_pos.le)) j

theorem round4_actual_uniform_weighted_normal_assembly
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius buffer c0 K3 : ℝ) (MT : ℝ≥0)
    (hbuffer : 0 < buffer) (hc0 : 0 < c0) (hK3 : 0 ≤ K3)
    (hdim : (m+1)*(m+2)/2 < N)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (A : X → D →L[ℝ] D →L[ℝ] ℝ) (O K : Set X) (center : X) :
    let Lip := round4ActualTemplateFieldLipschitz m N c0 K3 K3 hc0 hK3 hK3 MT
    let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
    let B := 2*(1+2*C.covectorBound)
    let I := 2*actualPhaseInverseConstant eta (2*C.covectorBound)
    let rhoN := round4NativeNormalRadius m N c0 B I C.restrictionReserve K3
    let cF := c0/B^2
    let cT := (C.restrictionReserve/(B^2*actualIncrementSortedSymmetricConstant m))^2
    let rho := round4UniformNormalRefinementRadius (N := N) templateDim R mu c H hmu hc buffer c0 K3 Lip
    let r := rho/actualPhaseRefinementFactor eta C.covectorBound
    let pieceBound := round4UniformNormalPieceBound (N := N) Ep templateDim R mu c H hmu hc
      modelRadius buffer c0 K3 MT hbuffer hc0 hK3
    let f := fun z => (round4ActualPhaseOperatorInChart F (fun _ => host) z,A z);
      IsOpen O → Convex ℝ O → (∀ z ∈ O, z.2 ∈ host.target) →
      ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O →
      ContDiffOn ℝ ∞ A O → (∀ z ∈ O, ‖fderiv ℝ A z‖₊ ≤ MT) →
      (∀ x ∈ O, ∀ v w, A x v w = A x w v) →
      K ⊆ closedBall center modelRadius →
      (∀ x ∈ K, ball x buffer ⊆ O) →
      (∀ x ∈ K, f x ∈ actualAllowedPhaseTensorData D V R mu c H) →
      (∀ z ∈ O, ∀ v : D, c0*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ host.symm) z.2 v‖^2) →
      (∀ k ≤ 3, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
        (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ K3) →
      ∃ (s : Finset X) (pick : s → C.indices)
        (charts : ∀ z : s, ∀ a, Round4UniformTemplateChart templateDim R mu c H hmu hc
          f O z.val rho (pick z) a) (W : Set X)
        (label : s × EdgePair (Module.finrank ℝ D+1) → ℕ),
        let chi := round4RefinementSquareCutoff X s r
        let amplitude := round4WeightedTemplateScalar C pick label chi A
        let xi := round4WeightedTemplateCovector C pick label
        let bound := pieceBound*Fintype.card (EdgePair (Module.finrank ℝ D+1))
        let cap := (round4TemplateHierarchy C)^bound
        (
          s.card ≤ pieceBound ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
          Function.Injective label ∧ (∀ q, label q < bound) ∧
          (∀ x ∈ W, ∑ z : s, chi z x ^ 2 = 1) ∧
          (∀ z : s, ContDiff ℝ ∞ (chi z)) ∧
          (∀ x : X, (activeCutoffIndices chi x).card ≤ 5^Module.finrank ℝ X) ∧
          (∀ (z : s) a, ContDiff ℝ ∞ (amplitude z a) ∧
            tsupport (amplitude z a) ⊆ (charts z a).chart.source) ∧
          (∀ x ∈ W, (∑ z : s, continuousRankOneReconstruct (xi z)
            (fun a => amplitude z a x ^ 2)) = (f x).2) ∧
          (∀ z a x, x ∈ tsupport (chi z) →
            LinearSecondFormGoodCovector (f x).1.toLinearMap (xi z a).toLinearMap) ∧
          (∀ z a x, x ∈ tsupport (chi z) →
            LinearSecondFormGoodCovector (f x).1.toLinearMap ((2 : ℝ) • xi z a).toLinearMap) ∧
          (∀ x (za zb : s × EdgePair (Module.finrank ℝ D+1)),
            x ∈ tsupport (chi za.1) → x ∈ tsupport (chi zb.1) → za ≠ zb →
            LinearSecondFormGoodCovector (f x).1.toLinearMap (xi za.1 za.2 + xi zb.1 zb.2).toLinearMap ∧
            LinearSecondFormGoodCovector (f x).1.toLinearMap (xi za.1 za.2 - xi zb.1 zb.2).toLinearMap) ∧
          (∀ z a, ‖xi z a‖ ≤ cap*C.covectorBound) ∧
          (∀ z a, ∃ (L : X ≃L[ℝ] X) (b : OpenPartialHomeomorph X X),
            b = (charts z a).chart.transHomeomorph L.toHomeomorph ∧
            b.source = (charts z a).chart.source ∧
            ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
            (∀ y ∈ b.source, (b y).1 = y.1 ∧ (b y).2 0 = xi z a y.2) ∧
            (∀ y ∈ b.target, (b.symm y).1 = y.1 ∧ xi z a (b.symm y).2 = y.2 0) ∧
            (∀ k y, y ∈ b.source → ‖iteratedFDeriv ℝ k b y‖ ≤
              (2*(1+2*cap))*‖iteratedFDeriv ℝ k (charts z a).chart y‖) ∧
            (∀ k y, y ∈ b.target → ‖iteratedFDeriv ℝ k b.symm y‖ ≤
              ‖iteratedFDeriv ℝ k (charts z a).chart.symm (L.symm y)‖*
                (2*actualPhaseInverseConstant 1 (2*cap))^k))
        ) ∧
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
                (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a) y)) ∧
          (∀ (j : ℕ) (Kj : ℝ), 0 ≤ Kj →
            (∀ k ≤ j+2, ∀ y ∈ O, ‖iteratedFDeriv ℝ k
              (fun v : X => F v.1 (host.symm v.2)) y‖ ≤ Kj) →
            ∀ (z : s) a k, k ≤ j → ∀ y ∈ round4NormalCutoffCarrier (charts z a).chart z.val rhoN,
              ‖iteratedFDeriv ℝ k (round4ActualNormalCarrierHostField F hF host (charts z a).chart
                (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a)) y‖ ≤
                round4NativeNormalHostConstant m N j cF cT B I Kj) ∧
          (∀ (z : s) (j : ℕ) (y : X), ‖iteratedFDeriv ℝ j (chi z) y‖ ≤
            round4UniformNormalCutoffProfile (N := N) Ep templateDim R mu c H hmu hc
              buffer c0 K3 MT hbuffer hc0 hK3 j) := by
  classical
  intro Lip C eta B I rhoN cF cT rho r pieceBound f
  have hRadius := round4UniformNormalRefinementRadius_spec (N := N)
    templateDim R mu c H hmu hc buffer c0 K3 Lip hbuffer hc0 hK3
  have hAssembly := Classical.choose_spec (round4_uniform_weighted_template_profiles_before_fields
    (Ep := Ep) templateDim R mu c H hmu hc modelRadius rho hRadius.1 Lip hRadius.2.2.1)
  intro hO hConv hOcoord hJoint hA hAT hsymm hKball hBuffer hAllowed hFirst hC3
  have hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ host.symm) y.2) z‖ ≤ K3 := by
    intro k hk z hz
    exact (spatial_first_jet_le hO hJoint hz k).trans (hC3 (k+1) (by omega) z hz)
  have hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ host.symm)) y.2) z‖ ≤ K3 := by
    intro k hk z hz
    exact (spatial_second_jet_le hO hJoint hz k).trans (hC3 (k+2) (by omega) z hz)
  have hLip := round4_actual_template_field_lipschitz F hF (fun _ => host) (fun _ => hhost)
    O hO hConv hOcoord hJoint c0 K3 K3 hc0 hK3 hK3 hFirst hAj hHj A MT
    (fun z hz => (hA.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) hAT
  have hbuffer' (z : X) (hz : z ∈ K) : ball z rho ⊆ O :=
    (ball_subset_ball hRadius.2.1).trans (hBuffer z hz)
  obtain ⟨s,pick,charts,W,label,hFacts,hCut⟩ := hAssembly f O K center hO hLip hA hsymm hKball hbuffer' hAllowed
  have hNormal := round4_actual_weighted_template_normal_family templateDim R mu c H hmu hc
    F hF host hhost O hO hOcoord hJoint A rho hRadius.1 s pick charts label
    c0 K3 hc0 hK3 hFirst hC3 hdim hRadius.2.2.2
  obtain ⟨data,hSupport,hSmooth,hLegal⟩ := hNormal
  refine ⟨s,pick,charts,W,label,hFacts,data,hSupport,hSmooth,hLegal,?_,hCut⟩
  intro j Kj hKj hJets z a k hk y hy
  exact round4_actual_template_normal_host_jets templateDim R mu c H hmu hc F hF host hhost
    O hO hJoint A z.val rho (pick z) a (charts z a) rhoN cF cT (data z a)
    j Kj hKj hJets k hk y hy

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_uniform_weighted_normal_assembly
