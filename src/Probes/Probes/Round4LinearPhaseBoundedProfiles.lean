import Probes.Round4LinearPhaseCoordinateEquiv

/-!
All-order profiles, including order zero, for the actual linear phase chart
restricted to the original open source. The inverse zero bound is the
original source coordinate bound, because its target is the actual image.
This is not an inference from a bound for d(phase) to a bound for phase.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def round4LinearPhaseForwardProfile (M V : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 2*(1+2*M)*V else if j = 1 then 2*(1+2*M) else 0

def round4LinearPhaseInverseProfile (mu M V : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then V else if j = 1 then 2*actualPhaseInverseConstant mu (2*M) else 0

theorem round4LinearPhaseForwardProfile_nonneg {M V : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (j : ℕ) : 0 ≤ round4LinearPhaseForwardProfile M V j := by
  unfold round4LinearPhaseForwardProfile
  split_ifs <;> positivity

theorem round4LinearPhaseInverseProfile_nonneg {mu M V : ℝ}
    (hmu : 0 < mu) (hM : 0 ≤ M) (hV : 0 ≤ V) (j : ℕ) :
    0 ≤ round4LinearPhaseInverseProfile mu M V j := by
  have hInv := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
  unfold round4LinearPhaseInverseProfile
  split_ifs <;> positivity

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round4_actual_linear_phase_bounded_chart
    (mu M V : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (xi : D →L[ℝ] ℝ) (hxi : mu ≤ ‖xi‖) (hxiM : ‖xi‖ ≤ M)
    (U : Set X) (hU : IsOpen U) (hV : ∀ z ∈ U, ‖z‖ ≤ V) :
    ∃ b : OpenPartialHomeomorph X X,
      b.source = U ∧ ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
      (∀ z ∈ b.source, (b z).1 = z.1 ∧ (b z).2 0 = xi z.2) ∧
      (∀ z ∈ b.target, (b.symm z).1 = z.1 ∧ xi (b.symm z).2 = z.2 0) ∧
      (∀ j z, z ∈ b.source → ‖iteratedFDeriv ℝ j b z‖ ≤ round4LinearPhaseForwardProfile M V j) ∧
      ∀ j z, z ∈ b.target → ‖iteratedFDeriv ℝ j b.symm z‖ ≤ round4LinearPhaseInverseProfile mu M V j := by
  obtain ⟨L, hL, hLi, hLf, hLinv⟩ := round4_actual_linear_phase_coordinate_equiv
    (Ep := Ep) mu M hmu hM xi hxi hxiM
  let b := L.toHomeomorph.toOpenPartialHomeomorph.restrOpen U hU
  have hsource : b.source = U := by change univ ∩ U = U; exact univ_inter U
  refine ⟨b, hsource, L.contDiff.contDiffOn, L.symm.contDiff.contDiffOn,
    fun z _ => hL z, fun z _ => hLi z, ?_, ?_⟩
  · intro j z hz
    have hzU : z ∈ U := hsource ▸ hz
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 0 L z‖ ≤ 2*(1+2*M)*V
      rw [norm_iteratedFDeriv_zero]
      exact (L.toContinuousLinearMap.le_of_opNorm_le hLf z).trans
        (mul_le_mul_of_nonneg_left (hV z hzU) (by positivity))
    | succ j =>
      cases j with
      | zero =>
        change ‖iteratedFDeriv ℝ 1 (L : X →L[ℝ] X) z‖ ≤ 2*(1+2*M)
        rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
        exact hLf
      | succ j =>
        change ‖iteratedFDeriv ℝ (j+1+1) (L : X →L[ℝ] X) z‖ ≤ 0
        rw [round4_continuous_linear_higher_jet_zero _ (j+1) (by omega) z, norm_zero]
  · intro j z hz
    have hzU : L.symm z ∈ U := hsource ▸ b.map_target hz
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 0 L.symm z‖ ≤ V
      rw [norm_iteratedFDeriv_zero]
      exact hV _ hzU
    | succ j =>
      cases j with
      | zero =>
        change ‖iteratedFDeriv ℝ 1 (L.symm : X →L[ℝ] X) z‖ ≤ 2*actualPhaseInverseConstant mu (2*M)
        rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
        exact hLinv
      | succ j =>
        change ‖iteratedFDeriv ℝ (j+1+1) (L.symm : X →L[ℝ] X) z‖ ≤ 0
        rw [round4_continuous_linear_higher_jet_zero _ (j+1) (by omega) z, norm_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_linear_phase_bounded_chart
