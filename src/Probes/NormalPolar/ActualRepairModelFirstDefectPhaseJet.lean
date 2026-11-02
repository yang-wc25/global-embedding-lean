import Probes.ActualIncrementJointDirectionalJets

/-! A phase derivative costs exactly the one derivative already present in
its primitive phase profile. No bound on the phase value is required. -/
noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_phase_directional_jets
    {Ep D : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (phi : Ep × D → ℝ) (v : D) (O S : Set (Ep × D)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hphi : ContDiffOn ℝ ∞ phi O) (j : ℕ) (ell Mphase : ℝ) (hell : 0 ≤ ell)
    (hb : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) phi z‖ ≤ Mphase) :
    ContDiffOn ℝ ∞ (fun z : Ep × D => fderiv ℝ (fun x => phi (z.1,x)) z.2 v) O ∧
    ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : Ep × D => fderiv ℝ (fun x => phi (w.1,x)) w.2 v) z‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ v‖*Mphase := by
  let first := fun z : Ep × D => fderiv ℝ (fun x => phi (z.1,x)) z.2
  let ev : (D →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hf := (incrementsJointSpatialJets_bridge phi O hO hphi).2.1
  refine ⟨ev.contDiff.comp_contDiffOn hf,?_⟩
  intro k hk z hz
  have hfirstb : ell^k*‖iteratedFDeriv ℝ k first z‖ ≤ Mphase :=
    (mul_le_mul_of_nonneg_left (spatial_first_jet_le hO hphi (hSO hz) k) (pow_nonneg hell k)).trans
      (hb k hk z hz)
  have hh := slow_linear_jet_bound ev O hO first hf k ell Mphase hell z (hSO hz) hfirstb
  simpa only [ev,first,Function.comp_def,ContinuousLinearMap.apply_apply] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_phase_directional_jets
