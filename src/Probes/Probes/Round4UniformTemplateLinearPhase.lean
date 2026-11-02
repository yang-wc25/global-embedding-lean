import Probes.Round4UniformTemplateRadius
import Probes.ActualPhaseEuclideanChart

/-!
Uniform first-derivative reserves for every covector in the numerical
dictionary provider, and their actual linear phase charts. The positive
lower bound is chosen before a map or atlas. The phases have zero higher
jets, so the same genuine adapted chart supplies all observation orders.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function
open scoped TensorProduct Topology ContDiff
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance linearPhaseRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance linearPhaseSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable (E V : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem round4_exists_uniform_template_covector_lower
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    ∃ eta > 0, ∀ (i : C.indices) a, eta ≤ ‖(C.template i).covectors a‖ := by
  classical
  let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
  obtain ⟨eta, heta, hbound⟩ := finite_positive_common_lower_bound
    (fun ia : C.indices × EdgePair (Module.finrank ℝ E + 1) =>
      ‖(C.template ia.1).covectors ia.2‖)
    (fun ia => norm_pos_iff.mpr ((C.template ia.1).covectors_ne_zero ia.2))
  exact ⟨eta, heta, fun i a => hbound (i,a)⟩

def round4UniformTemplateCovectorLower
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) : ℝ :=
  Classical.choose (round4_exists_uniform_template_covector_lower E V hdim R mu c H hmu hc)

theorem round4UniformTemplateCovectorLower_spec
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower E V hdim R mu c H hmu hc
    0 < eta ∧ ∀ (i : C.indices) a, eta ≤ ‖(C.template i).covectors a‖ :=
  Classical.choose_spec (round4_exists_uniform_template_covector_lower E V hdim R mu c H hmu hc)

theorem round4_continuous_linear_higher_jet_zero
    {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : Y →L[ℝ] Z) (k : ℕ) (hk : 1 ≤ k) (z : Y) :
    iteratedFDeriv ℝ (k+1) L z = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hder : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, hder]
  simp only [iteratedFDeriv_succ_const, Function.comp_apply, Pi.zero_apply]
  exact (continuousMultilinearCurryRightEquiv' ℝ (j+1) Y Z).symm.map_zero

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "W" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Actual linear phases from the fixed numerical provider admit one chart
for every higher order, with common numerical first and inverse bounds. -/
theorem round4_uniform_template_linear_phase_charts
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (i : (actualUniformPhaseTemplateProvider D W hdim R mu c H hmu hc).indices)
    (a : EdgePair (Module.finrank ℝ D + 1)) (z0 : X) (ell : ℝ) (hell : 0 < ell) :
    let C := actualUniformPhaseTemplateProvider D W hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D W hdim R mu c H hmu hc
    let psi := fun z : X => (C.template i).covectors a z.2
    let radius := actualEuclideanPhaseRadius eta C.covectorBound ell
    ∃ b : OpenPartialHomeomorph X X,
      ball z0 radius ⊆ b.source ∧ b.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
      (∀ z ∈ b.source, (b z).1 = z.1 ∧ (b z).2 0 = psi z) ∧
      (∀ z ∈ b.target, (b.symm z).1 = z.1 ∧ psi (b.symm z) = z.2 0) ∧
      closedBall (b z0) (radius / (4*actualPhaseInverseConstant eta (2*C.covectorBound)))
        ⊆ b.target ∧
      (∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ 2*(1+2*C.covectorBound)) ∧
      (∀ k, 1 ≤ k → ∀ z ∈ b.source, iteratedFDeriv ℝ (k+1) b z = 0) ∧
      ∀ (j : ℕ) (weight : ℝ), 0 < weight →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ b.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤
            actualEuclideanPhaseInverseJetCost eta C.covectorBound 0 j := by
  let C := actualUniformPhaseTemplateProvider D W hdim R mu c H hmu hc
  let eta := round4UniformTemplateCovectorLower D W hdim R mu c H hmu hc
  let xi := (C.template i).covectors a
  let L : X →L[ℝ] ℝ := xi.comp (ContinuousLinearMap.snd ℝ Ep D)
  have heta := round4UniformTemplateCovectorLower_spec D W hdim R mu c H hmu hc
  have hspatial : eta ≤ ‖(fderiv ℝ L z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖ := by
    rw [L.fderiv]
    have heq : L.comp (ContinuousLinearMap.inr ℝ Ep D) = xi := by ext v; rfl
    rw [heq]
    exact heta.2 i a
  have hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ L z‖ ≤ C.covectorBound := by
    intro z _
    rw [L.fderiv]
    exact ((ContinuousLinearMap.opNorm_comp_le xi (ContinuousLinearMap.snd ℝ Ep D)).trans
      (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_snd_le ℝ Ep D) (norm_nonneg xi)))).trans
          ((C.bounds i).2.2.2.2 a)
  have hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 L z‖ ≤ C.covectorBound := by
    intro z _
    rw [round4_continuous_linear_higher_jet_zero L 1 le_rfl z, norm_zero, mul_zero]
    exact C.covectorBound_pos.le
  obtain ⟨b, hb, hout, hs, hsi, hid, hiid, htarget, hhigh, hfirstb, _hweighted, hinv⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_pointwise_forward
      eta C.covectorBound heta.1 C.covectorBound_pos.le L z0 ell hell
      L.contDiff.contDiffOn hspatial hfirst hsecond
  refine ⟨b, hb, hout, hs, hsi, hid, hiid, htarget, hfirstb, ?_, ?_⟩
  · intro k hk z hz
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hh := hhigh k hk z hz
    simpa only [round4_continuous_linear_higher_jet_zero L k hk z, norm_zero, mul_zero] using hh
  · intro j weight hweight
    apply hinv j weight 0 hweight le_rfl
    intro k hk _ z _
    rw [round4_continuous_linear_higher_jet_zero L k hk z, norm_zero, mul_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_linear_phase_charts
