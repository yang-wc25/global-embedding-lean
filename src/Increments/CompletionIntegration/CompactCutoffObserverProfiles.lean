import CompletionIntegration.NativeCompactCutoffProfiles
import Repair.IncrementGivenPhaseTransitions
import Repair.IncrementCutoffObserverJets

/-!
# Actual compact cutoff jets on the original observer domains

Compactness is used only for the actual physical cutoff support in its own
host chart. The original observation domain remains unchanged and need not
be compact. On its active support the literal transition supplies the jets;
off that support the same cutoff has a zero germ. No coordinate-value bound
and no supplied observer-cutoff profile is required.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

private theorem completionCutoff_prefix_bound (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    {k j : ℕ} (hkj : k ≤ j) : C k ≤ bufferedTransitionPrefix C j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hC l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ,E) ∞ Y]

theorem completion_compact_cutoff_observer_profiles
    (q e : OpenPartialHomeomorph Y E)
    (hq : q ∈ maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (he : e ∈ maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (rho : Y → ℝ) (hRho : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ rho)
    (hCompact : IsCompact (tsupport rho)) (hSupport : tsupport rho ⊆ q.source)
    (S : Set E) (hS : S ⊆ e.target)
    (Transition : ℕ → ℝ) (hTransition : ∀ j, 0 ≤ Transition j)
    (hJets : ∀ z ∈ S, e.symm z ∈ tsupport rho → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (q ∘ e.symm) z‖ ≤ Transition j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ j z, z ∈ S →
        ell^j * ‖iteratedFDeriv ℝ j (rho ∘ e.symm) z‖ ≤ C j := by
  have hHost : ContDiffOn ℝ ∞ (rho ∘ q.symm) q.target :=
    (hRho.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hq)).contDiffOn
  obtain ⟨Host,hHost0,hHostJets⟩ := compact_supported_original_chart_profiles
    q rho hCompact hSupport hHost
  let C := repairEntranceCompositionProfile Host Transition
  have hC : ∀ j, 0 ≤ C j :=
    repairEntranceCompositionProfile_nonneg Host Transition hHost0 hTransition
  refine ⟨C,hC,?_⟩
  intro ell hell hell1 j z hz
  have hez := hS hz
  by_cases hActive : e.symm z ∈ tsupport rho
  · let t := e.symm.trans q
    have htz : z ∈ t.source := ⟨hez,hSupport hActive⟩
    have ht : ContDiffOn ℝ ∞ t t.source :=
      ((contMDiffOn_of_mem_maximalAtlas hq).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono (fun _ h => h.1))
        (fun _ h => h.2)).contDiffOn
    have hMap : MapsTo t t.source q.target := fun y hy => q.map_source hy.2
    have hBound := actual_fast_joint_chart_transfer Transition hTransition j t
      (rho ∘ q.symm) t.source q.target t.open_source q.open_target ht hHost hMap
      z htz 1 1 (bufferedTransitionPrefix Host j) zero_lt_one le_rfl (by
        intro k hkj
        simp only [one_pow,one_mul]
        have hh := (hHostJets 1 zero_le_one le_rfl k (t z) (hMap htz)).1
        simp only [one_pow,one_mul] at hh
        exact hh.trans (completionCutoff_prefix_bound Host hHost0 hkj)) (by
        intro k hk hkj
        simp only [one_pow,one_mul]
        exact hJets z hz hActive k hk)
    have hEq : (rho ∘ e.symm) =ᶠ[𝓝 z] ((rho ∘ q.symm) ∘ t) := by
      filter_upwards [t.open_source.mem_nhds htz] with w hw
      change rho (e.symm w) = rho (q.symm (q (e.symm w)))
      have hwq : e.symm w ∈ q.source := hw.2
      rw [q.left_inv hwq]
    have hActual : ‖iteratedFDeriv ℝ j (rho ∘ e.symm) z‖ ≤ C j := by
      rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
      simpa only [one_pow,one_mul,C,repairEntranceCompositionProfile] using hBound
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hActual
  · rw [iteratedFDeriv_comp_eq_zero_off_tsupport rho e.symm z
      (e.symm.continuousAt hez) hActive j,norm_zero,mul_zero]
    exact hC j

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.completion_compact_cutoff_observer_profiles
