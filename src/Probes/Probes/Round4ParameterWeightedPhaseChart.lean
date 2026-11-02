import Probes.Round4LinearPhaseCoordinateEquiv
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Probes.Round4WeightedTemplateFamily

/-!
The hierarchical phase weight is implemented by a genuine linear
postcomposition of the same adapted chart. The source is definitionally
unchanged, so this operation does not require a new cutoff cover or a new
refinement radius. A common upper bound for the weights controls both
derivatives. The phase kernel is unchanged by the positive scalar.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

private theorem weighted_phase_head_norm :
    ‖(EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0)‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x 0‖ ≤ 1*‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x 0
  · have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0).le_opNorm
      (EuclideanSpace.single 0 1)
    simpa using h

theorem round4Parameter_positive_phase_kernel
    (lambda : ℝ) (hlambda : 0 < lambda) (xi : D →L[ℝ] ℝ) :
    (lambda • xi).ker = xi.ker := by
  ext v
  change lambda * xi v = 0 ↔ xi v = 0
  simp only [mul_eq_zero, hlambda.ne', false_or]

private theorem weighted_chart_inverse_jet (L : X ≃L[ℝ] X) (f : X → X)
    (k : ℕ) (z : X) :
    ‖iteratedFDeriv ℝ k (f ∘ L.symm) z‖ ≤
      ‖iteratedFDeriv ℝ k f (L.symm z)‖*‖L.symm.toContinuousLinearMap‖^k := by
  have heq := L.symm.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := z) (mem_univ (L.symm z)) k
  simp only [preimage_univ, iteratedFDerivWithin_univ] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ k f (L.symm z)).norm_compContinuousLinearMap_le
      (fun _ : Fin k => L.symm.toContinuousLinearMap)

/-- A scalar or ambient-vector field on the fixed physical source must be
expressed by the actual inverse pullback in the new target coordinates. -/
theorem round4Parameter_weighted_source_field_coordinates {Y : Type*}
    (b : OpenPartialHomeomorph X X) (L : X ≃L[ℝ] X) (u : X → Y) :
    u ∘ (b.transHomeomorph L.toHomeomorph).symm = (u ∘ b.symm) ∘ L.symm := rfl

/-- The same source, actual chart and inverse, and actual weighted phase.
All constants precede the original chart and phase. -/
theorem round4Parameter_weighted_phase_chart_same_source
    (lambda cap : ℝ) (hlambda : 1 ≤ lambda) (hcap : lambda ≤ cap)
    (b : OpenPartialHomeomorph X X)
    (hb : ContDiffOn ℝ ∞ b b.source) (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (hp : ∀ z ∈ b.source, (b z).1 = z.1)
    (psi : X → ℝ) (hphase : ∀ z ∈ b.source, (b z).2 0 = psi z)
    (Bforward Binverse : ℝ) (hBinverse : 0 ≤ Binverse)
    (hforward : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bforward)
    (hinverse : ∀ z ∈ b.target, ‖fderiv ℝ b.symm z‖ ≤ Binverse) :
    ∃ (L : X ≃L[ℝ] X) (weighted : OpenPartialHomeomorph X X),
      weighted = b.transHomeomorph L.toHomeomorph ∧
      weighted.source = b.source ∧ weighted.target = L.symm ⁻¹' b.target ∧
      (∀ z, weighted z = L (b z)) ∧
      (∀ z, weighted.symm z = b.symm (L.symm z)) ∧
      ContDiffOn ℝ ∞ weighted weighted.source ∧
      ContDiffOn ℝ ∞ weighted.symm weighted.target ∧
      (∀ z ∈ weighted.source, (weighted z).1 = z.1 ∧
        (weighted z).2 0 = lambda * psi z) ∧
      (∀ z ∈ weighted.target, (weighted.symm z).1 = z.1 ∧
        lambda * psi (weighted.symm z) = z.2 0) ∧
      ‖L.toContinuousLinearMap‖ ≤ 2*(1+2*cap) ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ 2*actualPhaseInverseConstant 1 (2*cap) ∧
      (∀ z ∈ weighted.source, ‖fderiv ℝ weighted z‖ ≤
        (2*(1+2*cap))*Bforward) ∧
      (∀ z ∈ weighted.target, ‖fderiv ℝ weighted.symm z‖ ≤
        Binverse*(2*actualPhaseInverseConstant 1 (2*cap))) ∧
      (∀ k z, z ∈ weighted.source → ‖iteratedFDeriv ℝ k weighted z‖ ≤
        (2*(1+2*cap))*‖iteratedFDeriv ℝ k b z‖) ∧
      (∀ k z, z ∈ weighted.target → ‖iteratedFDeriv ℝ k weighted.symm z‖ ≤
        ‖iteratedFDeriv ℝ k b.symm (L.symm z)‖*
          (2*actualPhaseInverseConstant 1 (2*cap))^k) := by
  have hlampos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hcap0 : 0 ≤ cap := hlampos.le.trans hcap
  let xi : D →L[ℝ] ℝ := lambda • EuclideanSpace.proj 0
  have hxinorm : ‖xi‖ = lambda := by
    change ‖lambda • (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0)‖ = lambda
    rw [norm_smul, weighted_phase_head_norm, mul_one, Real.norm_eq_abs,
      abs_of_pos hlampos]
  obtain ⟨L,hL,hLi,hLf,hLinv⟩ := round4_actual_linear_phase_coordinate_equiv
    (Ep := Ep) 1 cap (by norm_num) hcap0 xi
    (by rw [hxinorm]; exact hlambda) (by rw [hxinorm]; exact hcap)
  let weighted := b.transHomeomorph L.toHomeomorph
  have hfwd (z : X) (hz : z ∈ weighted.source) :
      (weighted z).1 = z.1 ∧ (weighted z).2 0 = lambda * psi z := by
    refine ⟨(hL (b z)).1.trans (hp z hz), ?_⟩
    change (L (b z)).2 0 = lambda * psi z
    rw [(hL (b z)).2]
    change lambda * (b z).2 0 = lambda * psi z
    rw [hphase z hz]
  refine ⟨L,weighted,rfl,rfl,rfl,fun _ => rfl,fun _ => rfl,
    L.contDiff.comp_contDiffOn hb, hbi.comp L.symm.contDiff.contDiffOn (fun _ hz => hz),
    hfwd,?_,hLf,hLinv,?_,?_,?_,?_⟩
  · intro z hz
    have h := hfwd (weighted.symm z) (weighted.map_target hz)
    rw [weighted.right_inv hz] at h
    exact ⟨h.1.symm,h.2.symm⟩
  · intro z hz
    have hbz := (hb.contDiffAt (b.open_source.mem_nhds hz)).differentiableAt (by simp)
    change ‖fderiv ℝ (L ∘ b) z‖ ≤ _
    rw [fderiv_comp z L.differentiableAt hbz, ContinuousLinearEquiv.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hLf (hforward z hz) (norm_nonneg _) (by positivity))
  · intro z hz
    have hz' : L.symm z ∈ b.target := hz
    have hbz : DifferentiableAt ℝ b.symm (L.symm z) :=
      (hbi.contDiffAt (b.open_target.mem_nhds hz')).differentiableAt (by simp)
    change ‖fderiv ℝ (b.symm ∘ L.symm) z‖ ≤ _
    rw [fderiv_comp z hbz L.symm.differentiableAt, ContinuousLinearEquiv.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hinverse (L.symm z) hz) hLinv (norm_nonneg _) hBinverse)
  · intro k z hz
    change ‖iteratedFDeriv ℝ k (L.toContinuousLinearMap ∘ b) z‖ ≤ _
    exact (L.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (hb.contDiffAt (b.open_source.mem_nhds hz)) (by simp)).trans
      (mul_le_mul_of_nonneg_right hLf (norm_nonneg _))
  · intro k z hz
    change ‖iteratedFDeriv ℝ k (b.symm ∘ L.symm) z‖ ≤ _
    exact (weighted_chart_inverse_jet L b.symm k z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hLinv k) (norm_nonneg _))

open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance weightedChartRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance weightedChartSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- Actual hierarchical weighting of the already selected template chart.
The refinement source is unchanged. The supplied common label bound
supplies both numerical chart costs; finite refinement and coloring are
separate producers of that bound. -/
theorem round4Parameter_actual_hierarchical_template_chart
    [CompleteSpace Ep] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare D →L[ℝ] EuclideanSpace ℝ (Fin N)) ×
      (D →L[ℝ] D →L[ℝ] ℝ)) (O : Set X) (x : X) (ell : ℝ)
    (i : (actualUniformPhaseTemplateProvider D (EuclideanSpace ℝ (Fin N)) hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D+1))
    (block : Round4UniformTemplateChart hdim R mu c H hmu hc f O x ell i a)
    (level bound : ℕ) (hlevel : level ≤ bound) :
    let C := actualUniformPhaseTemplateProvider D (EuclideanSpace ℝ (Fin N)) hdim R mu c H hmu hc
    let lambda := (round4TemplateHierarchy C)^level
    let cap := (round4TemplateHierarchy C)^bound
    let eta := round4UniformTemplateCovectorLower D (EuclideanSpace ℝ (Fin N)) hdim R mu c H hmu hc
    ∃ (L : X ≃L[ℝ] X) (weighted : OpenPartialHomeomorph X X),
      weighted = block.chart.transHomeomorph L.toHomeomorph ∧
      weighted.source = block.chart.source ∧ weighted.target = L.symm ⁻¹' block.chart.target ∧
      (∀ z, weighted z = L (block.chart z)) ∧
      (∀ z, weighted.symm z = block.chart.symm (L.symm z)) ∧
      ContDiffOn ℝ ∞ weighted weighted.source ∧
      ContDiffOn ℝ ∞ weighted.symm weighted.target ∧
      (∀ z ∈ weighted.source, (weighted z).1 = z.1 ∧
        (weighted z).2 0 = (lambda • (C.template i).covectors a) z.2) ∧
      (∀ z ∈ weighted.target, (weighted.symm z).1 = z.1 ∧
        (lambda • (C.template i).covectors a) (weighted.symm z).2 = z.2 0) ∧
      ‖L.toContinuousLinearMap‖ ≤ 2*(1+2*cap) ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ 2*actualPhaseInverseConstant 1 (2*cap) ∧
      (∀ z ∈ weighted.source, ‖fderiv ℝ weighted z‖ ≤
        (2*(1+2*cap))*(2*(1+2*C.covectorBound))) ∧
      (∀ z ∈ weighted.target, ‖fderiv ℝ weighted.symm z‖ ≤
        (2*actualPhaseInverseConstant eta (2*C.covectorBound))*
          (2*actualPhaseInverseConstant 1 (2*cap))) ∧
      (∀ k z, z ∈ weighted.source → ‖iteratedFDeriv ℝ k weighted z‖ ≤
        (2*(1+2*cap))*‖iteratedFDeriv ℝ k block.chart z‖) ∧
      (∀ k z, z ∈ weighted.target → ‖iteratedFDeriv ℝ k weighted.symm z‖ ≤
        ‖iteratedFDeriv ℝ k block.chart.symm (L.symm z)‖*
          (2*actualPhaseInverseConstant 1 (2*cap))^k) := by
  intro C lambda cap eta
  have hLambda := round4TemplateHierarchy_gt_one C
  have hEta := (round4UniformTemplateCovectorLower_spec D (EuclideanSpace ℝ (Fin N))
    hdim R mu c H hmu hc).1
  have hInv := actualPhaseInverseConstant_one_le hEta
    (show 0 ≤ 2*C.covectorBound by have := C.covectorBound_pos; positivity)
  exact round4Parameter_weighted_phase_chart_same_source lambda cap
    (one_le_pow₀ hLambda.le) (pow_le_pow_right₀ hLambda.le hlevel)
    block.chart block.smooth block.inverse_smooth block.parameter_forward
    (fun z => (C.template i).covectors a z.2) block.phase_forward
    (2*(1+2*C.covectorBound)) (2*actualPhaseInverseConstant eta (2*C.covectorBound))
    (by positivity) block.forward_bound block.inverse_bound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_positive_phase_kernel
#print axioms GlobalEmbedding.Continuation.round4Parameter_weighted_phase_chart_same_source
#print axioms GlobalEmbedding.Continuation.round4Parameter_actual_hierarchical_template_chart
#print axioms GlobalEmbedding.Continuation.round4Parameter_weighted_source_field_coordinates
