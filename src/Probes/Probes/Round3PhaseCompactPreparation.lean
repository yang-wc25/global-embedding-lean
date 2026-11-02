import Probes.ActualOriginalPhaseProfileJets
import Probes.ActualOriginalHostRefinement
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Quantitative preparation of the actual phase on its compact carrier

The positive spatial margin, the total first- and second-derivative bounds,
and a genuine open buffer are produced from the actual smooth phase. They
are chosen together before every subsequent derivative order and scale.
This statement is for a fixed original packet: compactness does not assert
uniform conditioning of arbitrary phases from a best-phase bound alone.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {Ep Es : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [ProperSpace (Ep × Es)]

/-- All low-order inputs to the actual quantitative host refinement are
outputs of compact smooth noncritical phase data, on one common buffer. -/
theorem round3_actual_compact_phase_preparation
    (psi : Ep × Es → ℝ) (K U : Set (Ep × Es))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hpsi : ContDiffOn ℝ ∞ psi U)
    (hnonzero : ∀ x ∈ K,
      (fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es) ≠ 0) :
    ∃ (mu Mb R rho : ℝ) (O : Set (Ep × Es)),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < R ∧ 0 < rho ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      K ⊆ closedBall 0 R ∧
      (∀ x ∈ K, ball x rho ⊆ O) ∧
      ContDiffOn ℝ ∞ psi O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) ∧
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ Mb) ∧
      (∀ x ∈ O, rho * ‖iteratedFDeriv ℝ 2 psi x‖ ≤ Mb) := by
  have hfirst : ContinuousOn (fderiv ℝ psi) U :=
    hpsi.continuousOn_fderiv_of_isOpen hU (by simp)
  have hspatial : ContinuousOn
      (fun x => ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) K :=
    ((hfirst.clm_comp continuousOn_const).norm).mono hKU
  obtain ⟨mu, hmu, hmulower⟩ := hK.exists_forall_le' hspatial
    (fun x hx => norm_pos_iff.mpr (hnonzero x hx))
  obtain ⟨rho, hrho, hbuffer⟩ := hK.exists_cthickening_subset_open hU hKU
  let O := thickening rho K
  have hOK : O ⊆ cthickening rho K := thickening_subset_cthickening rho K
  have hOU : O ⊆ U := hOK.trans hbuffer
  have hcompact : IsCompact (cthickening rho K) := hK.cthickening
  obtain ⟨A, hA⟩ := hcompact.exists_bound_of_continuousOn (hfirst.mono hbuffer)
  have hsecond : ContinuousOn (iteratedFDeriv ℝ 2 psi) U := by
    apply (hpsi.continuousOn_iteratedFDerivWithin (m := 2) (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hU hx).symm
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn (hsecond.mono hbuffer)
  obtain ⟨R, hR, hRbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨mu, max 0 (max A (rho * B)), R, rho, O,
    hmu, le_max_left _ _, hR, hrho, isOpen_thickening,
    self_subset_thickening hrho K, hOU, ?_, ?_, hpsi.mono hOU,
    hmulower, ?_, ?_⟩
  · intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hRbound x hx
  · intro x hx
    exact ball_subset_thickening hx rho
  · intro x hx
    exact (hA x (hOK hx)).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x hx
    exact (mul_le_mul_of_nonneg_left (hB x (hOK hx)) hrho.le).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_actual_compact_phase_preparation
