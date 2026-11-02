import Probes.Round4LinearPhaseCoordinateEquiv

/-! A single genuine spatial linear coordinate equivalence is shared by
all parameter charts. Extracting the zero-parameter fiber of the actual
joint equivalence removes any irrelevant dependence on parameter coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))

theorem repair_reference_spatial_linear_phase
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (xi : D →L[ℝ] ℝ) (hxi : mu ≤ ‖xi‖) (hxiM : ‖xi‖ ≤ M) :
    ∃ L : D ≃L[ℝ] D,
      (∀ x, L x 0=xi x) ∧ (∀ y, xi (L.symm y)=y 0) ∧
      ‖(L : D →L[ℝ] D)‖ ≤ 2*(1+2*M) ∧
      ‖(L.symm : D →L[ℝ] D)‖ ≤ 2*actualPhaseInverseConstant mu (2*M) := by
  obtain ⟨J,hJ,hJi,hF,hI⟩ := round4_actual_linear_phase_coordinate_equiv
    (Ep := ℝ) mu M hmu hM xi hxi hxiM
  let ins : D →L[ℝ] (ℝ × D) := (0 : D →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ D)
  let f := (ContinuousLinearMap.snd ℝ ℝ D).comp (J.toContinuousLinearMap.comp ins)
  let g := (ContinuousLinearMap.snd ℝ ℝ D).comp (J.symm.toContinuousLinearMap.comp ins)
  have hf (x : D) : (0,f x)=J (0,x) := by
    apply Prod.ext
    · exact (hJ (0,x)).1.symm
    · rfl
  have hg (x : D) : (0,g x)=J.symm (0,x) := by
    apply Prod.ext
    · exact (hJi (0,x)).1.symm
    · rfl
  have hgf : LeftInverse g f := by
    intro x
    change (J.symm (0,f x)).2=x
    rw [hf,J.symm_apply_apply]
  have hfg : RightInverse g f := by
    intro x
    change (J (0,g x)).2=x
    rw [hg,J.apply_symm_apply]
  let L := ContinuousLinearEquiv.equivOfInverse f g hgf hfg
  refine ⟨L,fun x => (hJ (0,x)).2,fun x => (hJi (0,x)).2,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖(J (0,x)).2‖ ≤ _
    calc
      ‖(J (0,x)).2‖ ≤ ‖J (0,x)‖ := norm_snd_le _
      _ ≤ (2*(1+2*M))*‖(0,x)‖ := J.toContinuousLinearMap.le_of_opNorm_le hF _
      _ = (2*(1+2*M))*‖x‖ := by simp
  · have hInv := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖(J.symm (0,x)).2‖ ≤ _
    calc
      ‖(J.symm (0,x)).2‖ ≤ ‖J.symm (0,x)‖ := norm_snd_le _
      _ ≤ (2*actualPhaseInverseConstant mu (2*M))*‖(0,x)‖ :=
        J.symm.toContinuousLinearMap.le_of_opNorm_le hI _
      _ = (2*actualPhaseInverseConstant mu (2*M))*‖x‖ := by simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_spatial_linear_phase
