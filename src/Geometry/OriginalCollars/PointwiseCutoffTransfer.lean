import CompletionIntegration.CompactCutoffObserverProfiles

/-!
# Explicit finite host jets transfer to original cutoff observations

Only the displayed finite host jet bound is read.  On active support the
literal transition transports that bound; off topological support every
jet of the same scalar is zero.  No supremum of actual derivatives or
compact-profile choice occurs in the formula.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalCollars

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ,E) ∞ Y]

theorem cutoff_observer_bound_from_explicit_host_jets
    (q e : OpenPartialHomeomorph Y E)
    (hq : q ∈ maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (rho : Y → ℝ) (hRho : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ rho)
    (hSupport : tsupport rho ⊆ q.source)
    (Transition : ℕ → ℝ) (hTransition : ∀ k, 0 ≤ Transition k)
    (j : ℕ) (H : ℝ) (hH : 0 ≤ H) (z : E) (hz : z ∈ e.target)
    (hHostJets : e.symm z ∈ tsupport rho → ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k (rho ∘ q.symm) (q (e.symm z))‖ ≤ H)
    (hTransitionJets : e.symm z ∈ tsupport rho → ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (q ∘ e.symm) z‖ ≤ Transition k) :
    ‖iteratedFDeriv ℝ j (rho ∘ e.symm) z‖ ≤ actualFastChartTransferCost Transition j * H := by
  have hHost : ContDiffOn ℝ ∞ (rho ∘ q.symm) q.target :=
    (hRho.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hq)).contDiffOn
  by_cases hActive : e.symm z ∈ tsupport rho
  · let t := e.symm.trans q
    have htz : z ∈ t.source := ⟨hz,hSupport hActive⟩
    have ht : ContDiffOn ℝ ∞ t t.source :=
      ((contMDiffOn_of_mem_maximalAtlas hq).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono (fun _ h => h.1))
        (fun _ h => h.2)).contDiffOn
    have hMap : MapsTo t t.source q.target := fun y hy => q.map_source hy.2
    have hBound := actual_fast_joint_chart_transfer Transition hTransition j t
      (rho ∘ q.symm) t.source q.target t.open_source q.open_target ht hHost hMap
      z htz 1 1 H zero_lt_one le_rfl
      (by intro k hkj; simpa only [one_pow,one_mul,t,OpenPartialHomeomorph.coe_trans,Function.comp_apply]
        using hHostJets hActive k hkj)
      (by intro k hk hkj; simpa only [one_pow,one_mul,t,OpenPartialHomeomorph.coe_trans]
        using hTransitionJets hActive k hk hkj)
    have hEq : (rho ∘ e.symm) =ᶠ[𝓝 z] ((rho ∘ q.symm) ∘ t) := by
      filter_upwards [t.open_source.mem_nhds htz] with w hw
      change rho (e.symm w) = rho (q.symm (q (e.symm w)))
      have hwq : e.symm w ∈ q.source := hw.2
      rw [q.left_inv hwq]
    rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa only [one_pow,one_mul] using hBound
  · rw [iteratedFDeriv_comp_eq_zero_off_tsupport rho e.symm z
      (e.symm.continuousAt hz) hActive j,norm_zero]
    exact mul_nonneg (actualFastChartTransferCost_nonneg Transition hTransition j) hH

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.cutoff_observer_bound_from_explicit_host_jets
