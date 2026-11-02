import Repair.ReferenceChartCutoffExtension
import Repair.EntranceCompositionProfiles
import GlobalEmbedding.Offline.BoundedSquareCutoffSum

/-! The globally zero-extended actual owner cutoff has uniform derivatives
in every genuine observer chart.  Outside its actual support every jet is
zero; on its support only original transition derivatives are read. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private theorem repairCutoffPrefix_bound (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    {k j : ℕ} (hkj : k ≤ j) : A k ≤ bufferedTransitionPrefix A j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hA l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace E Y] [IsManifold 𝓘(ℝ,E) ∞ Y]

theorem repair_zero_extended_cutoff_observer_jets
    (owner observer : OpenPartialHomeomorph Y E)
    (hOwner : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (hObserver : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (phi : E → ℝ) (hPhi : ContDiff ℝ ∞ phi)
    (hCompact : IsCompact (tsupport phi)) (hTarget : tsupport phi ⊆ owner.target)
    (Scalar Transition : ℕ → ℝ)
    (hScalar : ∀ j, 0 ≤ Scalar j) (hTransition : ∀ j, 0 ≤ Transition j)
    (hScalarJets : ∀ j y, ‖iteratedFDeriv ℝ j phi y‖ ≤ Scalar j)
    (z : E) (hz : z ∈ observer.target)
    (hTransitionJets : observer.symm z ∈ owner.source → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ Transition j)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (repairReferenceChartCutoff owner phi ∘ observer.symm) z‖ ≤
      repairEntranceCompositionProfile Scalar Transition j := by
  let chi := repairReferenceChartCutoff owner phi
  have hCost := repairEntranceCompositionProfile_nonneg Scalar Transition hScalar hTransition j
  by_cases hActive : observer.symm z ∈ tsupport chi
  · have hown := ((repair_reference_chart_cutoff_support owner phi hCompact hTarget).2 hActive).1
    let t := observer.symm.trans owner
    have htz : z ∈ t.source := ⟨hz,hown⟩
    have ht : ContDiffOn ℝ ∞ t t.source :=
      ((contMDiffOn_of_mem_maximalAtlas hOwner).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hObserver).mono (fun _ h => h.1))
        (fun _ h => h.2)).contDiffOn
    have heq : chi ∘ observer.symm =ᶠ[𝓝 z] phi ∘ t := by
      filter_upwards [t.open_source.mem_nhds htz] with y hy
      exact repair_reference_chart_cutoff_on_source owner phi hy.2
    rw [(heq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    have hb := actual_fast_joint_chart_transfer Transition hTransition j t phi t.source univ
      t.open_source isOpen_univ ht hPhi.contDiffOn (fun _ _ => mem_univ _) z htz
      1 1 (bufferedTransitionPrefix Scalar j) zero_lt_one le_rfl (by
        intro k hk
        simp only [one_pow,one_mul]
        exact (hScalarJets k (t z)).trans (repairCutoffPrefix_bound Scalar hScalar hk)) (by
        intro k hk _
        simp only [one_pow,one_mul]
        exact hTransitionJets hown k hk)
    simpa only [one_pow,one_mul,repairEntranceCompositionProfile] using hb
  · rw [iteratedFDeriv_comp_eq_zero_off_tsupport chi observer.symm z
      (observer.symm.continuousAt hz) hActive j,norm_zero]
    exact hCost

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_zero_extended_cutoff_observer_jets
