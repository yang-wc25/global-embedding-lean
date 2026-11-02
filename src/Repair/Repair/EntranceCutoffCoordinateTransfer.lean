import Repair.EntranceRehostedProfiles

/-!
# The literal cutoff in adapted coordinates from its original derivatives

Only the scalar cutoff and the actual inverse transition are differentiated.
The identity on the true target follows from the two partial homeomorphisms;
there is no one-phase jet hypothesis for transverse chart coordinates.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Q : Type*} [TopologicalSpace Q]

private theorem entranceCutoff_prefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

theorem repairEntrance_actual_cutoff_coordinate_transfer
    (original adapted : OpenPartialHomeomorph Q X) (eta : Q → ℝ)
    (Cutoff Inverse : ℕ → ℝ) (hCutoff : ∀ j, 0 ≤ Cutoff j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (hSmooth : ContDiffOn ℝ ∞ (eta ∘ original.symm) (original.symm.trans adapted).source)
    (hInvSmooth : ContDiffOn ℝ ∞ (original.symm.trans adapted).symm (original.symm.trans adapted).target)
    (j : ℕ) (z : X) (hz : z ∈ (original.symm.trans adapted).source)
    (hOriginalJets : ∀ k, k ≤ j → ‖iteratedFDeriv ℝ k (eta ∘ original.symm) z‖ ≤ Cutoff k)
    (hInverseJets : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (original.symm.trans adapted).symm ((original.symm.trans adapted) z)‖ ≤ Inverse k) :
    ‖iteratedFDeriv ℝ j (eta ∘ adapted.symm) ((original.symm.trans adapted) z)‖ ≤
      repairEntranceCompositionProfile Cutoff Inverse j := by
  let t := original.symm.trans adapted
  have ht : t z ∈ t.target := t.map_source hz
  have hEq : (eta ∘ adapted.symm) =ᶠ[𝓝 (t z)] ((eta ∘ original.symm) ∘ t.symm) := by
    filter_upwards [t.open_target.mem_nhds ht] with w hw
    change eta (adapted.symm w) = eta (original.symm (original (adapted.symm w)))
    rw [original.left_inv hw.2]
  have hBound := actual_fast_joint_chart_transfer Inverse hInverse j t.symm (eta ∘ original.symm)
    t.target t.source t.open_target t.open_source hInvSmooth hSmooth t.symm.mapsTo
    (t z) ht 1 1 (bufferedTransitionPrefix Cutoff j) zero_lt_one le_rfl (by
      intro k hk
      rw [t.left_inv hz]
      simp only [one_pow,one_mul]
      exact (hOriginalJets k hk).trans (entranceCutoff_prefix_bound Cutoff hCutoff hk)) (by
      intro k hk hkj
      simpa only [one_pow,one_mul] using hInverseJets k hk hkj)
  rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
  simpa only [one_pow,one_mul,repairEntranceCompositionProfile] using hBound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_cutoff_coordinate_transfer
