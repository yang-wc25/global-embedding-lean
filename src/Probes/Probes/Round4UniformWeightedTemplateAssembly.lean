import Probes.Round4ParameterWeightedPhaseChart

/-!
The numerical class chooses its total refinement bound before the actual
field. The same finite square-cutoff construction then supplies bounded
labels, genuine weighted phases, exact tensor reconstruction, good signed
interactions, and source-preserving weighted charts with all-order costs.
The label bound comes from the proved total finite refinement bound, not
from the pointwise cutoff multiplicity. This is one host; cross-host
coloring and the complete original reference packet remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function
open scoped TensorProduct Topology ContDiff NNReal BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance weightedAssemblyRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance weightedAssemblySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance weightedAssemblyTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance weightedAssemblyTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem round4_uniform_weighted_template_assembly_before_fields
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius rho : ℝ) (hrho : 0 < rho) (Lip : ℝ≥0)
    (hradius : rho ≤ round4UniformTemplateRadius D V hdim R mu c H hmu hc / ((Lip : ℝ)+1)) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc
    let r := rho/actualPhaseRefinementFactor eta C.covectorBound
    ∃ pieceBound : ℕ, ∀
      (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
      (O K : Set X) (center : X),
      IsOpen O → LipschitzOnWith Lip f O →
      ContDiffOn ℝ ∞ (fun x => (f x).2) O →
      (∀ x ∈ O, ∀ v w, (f x).2 v w = (f x).2 w v) →
      K ⊆ closedBall center modelRadius →
      (∀ x ∈ K, ball x rho ⊆ O) →
      (∀ x ∈ K, f x ∈ actualAllowedPhaseTensorData D V R mu c H) →
      ∃ (s : Finset X) (pick : s → C.indices)
        (charts : ∀ x : s, ∀ a, Round4UniformTemplateChart hdim R mu c H hmu hc
          f O x.val rho (pick x) a) (W : Set X)
        (label : s × EdgePair (Module.finrank ℝ D+1) → ℕ),
        let chi := round4RefinementSquareCutoff X s r
        let amplitude := round4WeightedTemplateScalar C pick label chi (fun x => (f x).2)
        let xi := round4WeightedTemplateCovector C pick label
        let bound := pieceBound*Fintype.card (EdgePair (Module.finrank ℝ D+1))
        let cap := (round4TemplateHierarchy C)^bound
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
              (2*actualPhaseInverseConstant 1 (2*cap))^k)) := by
  classical
  intro C eta r
  have hr : 0 < r := div_pos hrho (actualPhaseRefinementFactor_pos
    (round4UniformTemplateCovectorLower_spec D V hdim R mu c H hmu hc).1 C.covectorBound_pos.le)
  obtain ⟨pieceBound,hFamily⟩ := round4_uniform_template_square_family_before_fields
    (Ep := Ep) hdim R mu c H hmu hc modelRadius rho hrho Lip hradius
  refine ⟨pieceBound, ?_⟩
  intro f O K center hO hf hg hsymm hKball hbuffer hallowed
  obtain ⟨s,pick,charts,W,hcard,hsK,hW,hKW,hpart,hsm,hcount,hcut,hamp,hreconstruct⟩ :=
    hFamily f O K center hO hf hg hsymm hKball hbuffer hallowed
  let chi := round4RefinementSquareCutoff X s r
  have hsupport (z : s) (a : EdgePair (Module.finrank ℝ D+1)) :
      tsupport (chi z) ⊆ (charts z a).chart.source := by
    apply (tensorLocalNormalizedCutoff_tsupport_subset
      (fun q : s => actualRefinementBump X r q.val) z).trans
    rw [actualRefinementBump_tsupport X r hr z.val]
    apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
    have hrad : 4*r = actualEuclideanPhaseRadius eta C.covectorBound rho :=
      actualPhaseRefinementFactor_radius eta C.covectorBound rho
    rw [hrad]
    exact (charts z a).inner
  let a0 : EdgePair (Module.finrank ℝ D+1) :=
    ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ) < 1; omega⟩
  have hdom (z : s) (x : X) (hx : x ∈ tsupport (chi z)) :
      (f x).2 ∈ (C.template (pick z)).tensorDomain :=
    (charts z a0).tensor_domain x (hsupport z a0 hx)
  obtain ⟨label,hinj,hlabel⟩ := round4_bounded_host_template_labels
    (E := D) (ι := s) pieceBound (by simpa using hcard)
  have hSmooth := round4_weighted_template_smooth C pick label chi (fun x => (f x).2)
    O hO hsm hg (fun z => (hsupport z a0).trans (charts z a0).source_domain) hdom
  have hGood := round4_weighted_template_interactions_on_support C pick label chi (fun x => (f x).1)
    (fun z x hx => (charts z a0).operator_domain x (hsupport z a0 hx))
    (fun x za zb hza hzb hne => fun heq => hne (hinj heq))
  refine ⟨s,pick,charts,W,label,hcard,hsK,hW,hKW,hinj,hlabel,hpart,hsm,hcount,?_,?_,
    hGood.1,hGood.2.1,hGood.2.2,?_,?_⟩
  · intro z a
    exact ⟨(hSmooth z a).1,(hSmooth z a).2.trans (hsupport z a)⟩
  · intro x hx
    exact round4_weighted_template_reconstruct C pick label chi (fun x => (f x).2)
      x (hpart x hx) (fun z => hdom z x)
      (fun z hz => hsymm x ((charts z a0).source_domain (hsupport z a0 hz)))
  · intro z a
    exact round4_weighted_template_covector_bound C pick label _
      (fun q => (hlabel q).le) z a
  · intro z a
    obtain ⟨L,b,hdef,hsource,htarget,hforward,hinverse,hb,hbi,hphase,hback,
      hLf,hLi,hBd,hBid,hjets,hinvjets⟩ := round4Parameter_actual_hierarchical_template_chart
      hdim R mu c H hmu hc f O z.val rho (pick z) a (charts z a)
      (label (z,a)) (pieceBound*Fintype.card (EdgePair (Module.finrank ℝ D+1)))
      (hlabel (z,a)).le
    exact ⟨L,b,hdef,hsource,hb,hbi,hphase,hback,hjets,hinvjets⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_weighted_template_assembly_before_fields
