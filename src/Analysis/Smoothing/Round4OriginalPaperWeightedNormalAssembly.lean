import Smoothing.Round4UniformWeightedNormalAssembly
import Smoothing.Round4OriginalFiniteNativeJets
import Smoothing.Round4OriginalC3NativeJets

/-! The original paperAtlasCj 3 on its actual original sample set supplies
the native joint C3 budget consumed by the SAME template normal factory.
The model comparison is explicit; no adapted reserve or geometry is added. -/

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
variable {d m N cParam : ℕ} {P : Type*} [TopologicalSpace P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
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

theorem round4_original_paper_weighted_normal_assembly
    (Aatlas : BufferedAtlas M D) (Bparam : Fin cParam → OpenPartialHomeomorph P Ep)
    (F : P × M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F (p,x)))
    (S : Fin Aatlas.count × Fin cParam → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Aatlas Bparam i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Aatlas Bparam F i)
      (incrementsOriginalDifferentiation Aatlas Bparam i))
    (R3 : ℝ) (hR3 : 0 ≤ R3)
    (hC3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates Aatlas Bparam F)
      (incrementsOriginalDifferentiation Aatlas Bparam) S ≤ ENNReal.ofReal R3)
    (i : Fin Aatlas.count × Fin cParam)
    (hhost : Aatlas.chart i.1 ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius buffer c0 : ℝ) (MT : ℝ≥0)
    (hbuffer : 0 < buffer) (hc0 : 0 < c0) (hdim : (m+1)*(m+2)/2 < N)
    (T : X → D →L[ℝ] D →L[ℝ] ℝ) (O K : Set X) (center : X) :
    let Fn := fun p x => F ((Bparam i.2).symm p,x)
    let hFn := fun p => hF ((Bparam i.2).symm p)
    let host := Aatlas.chart i.1
    let K3 := actualOriginalMapJetCost (m+1) d N 1*R3
    let hK3 := mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 1) hR3
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
    let f := fun z => (round4ActualPhaseOperatorInChart Fn (fun _ => host) z,T z);
      IsOpen O → Convex ℝ O →
      (∀ z ∈ O, parameterTensorModelEquiv (m+1) d z ∈ S i) →
      ContDiffOn ℝ ∞ T O → (∀ z ∈ O, ‖fderiv ℝ T z‖₊ ≤ MT) →
      (∀ x ∈ O, ∀ v w, T x v w = T x w v) →
      K ⊆ closedBall center modelRadius →
      (∀ x ∈ K, ball x buffer ⊆ O) →
      (∀ x ∈ K, f x ∈ actualAllowedPhaseTensorData D V R mu c H) →
      (∀ z ∈ O, ∀ v : D, c0*‖v‖^2 ≤ ‖fderiv ℝ (Fn z.1 ∘ host.symm) z.2 v‖^2) →
      ∃ (s : Finset X) (pick : s → C.indices)
        (charts : ∀ z : s, ∀ a, Round4UniformTemplateChart templateDim R mu c H hmu hc
          f O z.val rho (pick z) a) (W : Set X)
        (label : s × EdgePair (Module.finrank ℝ D+1) → ℕ),
        let chi := round4RefinementSquareCutoff X s r
        let amplitude := round4WeightedTemplateScalar C pick label chi T
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
        ∃ data : ∀ (z : s) a, Round4ActualNormalCarrier Fn hFn host (charts z a).chart
          (fun y => (C.template (pick z)).covectors a (host y.2)) z.val rhoN cF cT,
          (∀ (z : s) a, tsupport (chi z) ⊆
            round4NormalCutoffCarrier (charts z a).chart z.val rhoN) ∧
          (∀ (z : s) a, ContDiffOn ℝ ∞
            (round4ActualNormalCarrierHostField Fn hFn host (charts z a).chart
              (fun y => (C.template (pick z)).covectors a (host y.2)) z.val rhoN cF cT (data z a))
            (round4NormalCutoffCarrier (charts z a).chart z.val rhoN)) ∧
          (∀ (z : s) a y, y ∈ round4NormalCutoffCarrier (charts z a).chart z.val rhoN →
            Round4PhaseNormalAt Fn hFn
              (fun p => round4WeightedTemplateCovector C pick label z a (host p.2))
              (y.1,host.symm y.2)
              (round4ActualNormalCarrierHostField Fn hFn host (charts z a).chart
                (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a) y)) ∧
          (∀ (j : ℕ) (Rj : ℝ), 0 ≤ Rj →
            paperAtlasCj (j+2) (incrementsOriginalMapCoordinates Aatlas Bparam F)
              (incrementsOriginalDifferentiation Aatlas Bparam) S ≤ ENNReal.ofReal Rj →
            ∀ (z : s) a k, k ≤ j → ∀ y ∈ round4NormalCutoffCarrier (charts z a).chart z.val rhoN,
              ‖iteratedFDeriv ℝ k (round4ActualNormalCarrierHostField Fn hFn host (charts z a).chart
                (fun p => (C.template (pick z)).covectors a (host p.2)) z.val rhoN cF cT (data z a)) y‖ ≤
                round4NativeNormalHostConstant m N j cF cT B I
                  (actualOriginalMapJetCost (m+1) d N j*Rj)) ∧
          (∀ (z : s) (j : ℕ) (y : X), ‖iteratedFDeriv ℝ j (chi z) y‖ ≤
            round4UniformNormalCutoffProfile (N := N) Ep templateDim R mu c H hmu hc
              buffer c0 K3 MT hbuffer hc0 hK3 j) := by
  classical
  intro Fn hFn host K3 hK3 Lip C eta B I rhoN cF cT rho r pieceBound f
  intro hO hConv hSample hT hTT hsymm hKball hBuffer hAllowed hFirst
  have hJoint : ContDiffOn ℝ ∞ (fun z : X => Fn z.1 (host.symm z.2)) O :=
    round4_original_native_host_joint_smooth Aatlas Bparam F S hSO hCoords i O hSample
  have hOcoord (z : X) (hz : z ∈ O) : z.2 ∈ host.target :=
    round4_original_native_host_target Aatlas Bparam S hSO i z (hSample z hz)
  have hNativeC3 : ∀ k ≤ 3, ∀ z ∈ O,
      ‖iteratedFDeriv ℝ k (fun y : X => Fn y.1 (host.symm y.2)) z‖ ≤ K3 := by
    intro k hk z hz
    exact round4_original_C3_native_joint_jets Aatlas Bparam F S hSO hCoords R3 hR3 hC3
      i k hk z (hSample z hz)
  obtain ⟨s,pick,charts,W,label,hFacts,data,hSupport,hSmooth,hLegal,hHigh,hCut⟩ :=
    round4_actual_uniform_weighted_normal_assembly templateDim R mu c H hmu hc
      modelRadius buffer c0 K3 MT hbuffer hc0 hK3 hdim Fn hFn host hhost T O K center
      hO hConv hOcoord hJoint hT hTT hsymm hKball hBuffer hAllowed hFirst hNativeC3
  refine ⟨s,pick,charts,W,label,hFacts,data,hSupport,hSmooth,hLegal,?_,hCut⟩
  intro j Rj hRj hCj z a k hk y hy
  apply hHigh j (actualOriginalMapJetCost (m+1) d N j*Rj)
    (mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N j) hRj) ?_ z a k hk y hy
  intro l hl v hv
  exact round4_original_finite_native_joint_jets Aatlas Bparam F S hSO hCoords j Rj hRj hCj
    i l hl v (hSample v hv)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_paper_weighted_normal_assembly
