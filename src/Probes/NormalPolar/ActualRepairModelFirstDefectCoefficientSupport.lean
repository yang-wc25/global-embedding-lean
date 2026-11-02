import NormalPolar.ActualRepairModelFirstDefectCoefficient

/-! Support of a genuine physical coefficient is inherited from both complete
amplitude zero germs. No phase derivative or phase regularity is required at
an inactive point. -/
noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_coefficient_support_of_amplitudes
    {P Ep Label : Type*} [TopologicalSpace P]
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
    (phase : Label → P → ℝ) (tau : ℝ)
    (R Q : Label → P → EuclideanSpace ℝ (Fin N))
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : Ep × EuclideanSpace ℝ (Fin (m+1)) → P)
    (z : Ep × EuclideanSpace ℝ (Fin (m+1))) (hkappa : ContinuousAt kappa z)
    (hzW : kappa z ∈ W) (l : Label)
    (hsupport : z ∈ tsupport (fun w => incrementsSecondaryPhysicalCoefficient
      (fun l b x => phase l (kappa (b,x))) tau (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x)))
      (fun l b (_ : Unit) x => Q l (kappa (b,x)))
      (fun i _ => EuclideanSpace.single i 1) w l)) :
    kappa z ∈ K l := by
  by_contra hn
  have hr := parameterRound2_relative_observation_zero_germ (R l) W (K l) hW (hRsupport l)
    kappa z hkappa hzW hn
  have hq := parameterRound2_relative_observation_zero_germ (Q l) W (K l) hW (hQsupport l)
    kappa z hkappa hzW hn
  have hc := round4_complete_observed_coefficient_zero_germ (R l ∘ kappa) (Q l ∘ kappa)
    (phase l ∘ kappa) tau (fun i : Fin (m+1) => EuclideanSpace.single i 1) z hr hq
  exact (notMem_tsupport_iff_eventuallyEq.mpr hc) hsupport

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_coefficient_support_of_amplitudes
