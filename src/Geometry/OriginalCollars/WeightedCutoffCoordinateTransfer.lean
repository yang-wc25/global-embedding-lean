import Repair.EntranceCutoffCoordinateTransfer

/-!
# The literal adapted cutoff at the current slow scale

Only weighted original scalar jets and positive weighted inverse-transition
jets at the same physical point enter.  The current scale is retained in
both hypotheses and conclusion.  There is no scale-one norm or coordinate
value assumption, and no loss by an extra negative power of the scale.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.OriginalCollars

private theorem weightedCutoff_prefix_bound (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    {k j : ℕ} (hkj : k ≤ j) : C k ≤ bufferedTransitionPrefix C j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hC l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Q : Type*} [TopologicalSpace Q]

theorem actual_cutoff_coordinate_transfer_at_scale
    (original adapted : OpenPartialHomeomorph Q X) (eta : Q → ℝ)
    (Cutoff Inverse : ℕ → ℝ) (hCutoff : ∀ k, 0 ≤ Cutoff k) (hInverse : ∀ k, 0 ≤ Inverse k)
    (hSmooth : ContDiffOn ℝ ∞ (eta ∘ original.symm) (original.symm.trans adapted).source)
    (hInvSmooth : ContDiffOn ℝ ∞ (original.symm.trans adapted).symm (original.symm.trans adapted).target)
    (ell : ℝ) (hell : 0 < ell) (j : ℕ) (z : X)
    (hz : z ∈ (original.symm.trans adapted).source)
    (hOriginalJets : ∀ k, k ≤ j →
      ell^k * ‖iteratedFDeriv ℝ k (eta ∘ original.symm) z‖ ≤ Cutoff k)
    (hInverseJets : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k (original.symm.trans adapted).symm
        ((original.symm.trans adapted) z)‖ ≤ Inverse k) :
    ell^j * ‖iteratedFDeriv ℝ j (eta ∘ adapted.symm) ((original.symm.trans adapted) z)‖ ≤
      repairEntranceCompositionProfile Cutoff Inverse j := by
  let t := original.symm.trans adapted
  have ht : t z ∈ t.target := t.map_source hz
  have hEq : (eta ∘ adapted.symm) =ᶠ[𝓝 (t z)] ((eta ∘ original.symm) ∘ t.symm) := by
    filter_upwards [t.open_target.mem_nhds ht] with w hw
    change eta (adapted.symm w) = eta (original.symm (original (adapted.symm w)))
    have hwOriginal : adapted.symm w ∈ original.source := hw.2
    rw [original.left_inv hwOriginal]
  have hBound := actual_fast_joint_chart_transfer Inverse hInverse j t.symm (eta ∘ original.symm)
    t.target t.source t.open_target t.open_source hInvSmooth hSmooth t.symm.mapsTo
    (t z) ht ell ell (bufferedTransitionPrefix Cutoff j) hell le_rfl (by
      intro k hk
      rw [t.left_inv hz]
      exact (hOriginalJets k hk).trans (weightedCutoff_prefix_bound Cutoff hCutoff hk))
    (fun k hk hkj => hInverseJets k hk hkj)
  rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
  simpa only [repairEntranceCompositionProfile] using hBound

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.actual_cutoff_coordinate_transfer_at_scale
