import Repair.EndpointCutoffObserverJets
import Repair.EndpointOriginalLinearCoordinates

/-! A field defined by an actual local host formula is estimated on its
original open carrier in every observer chart.  The bound reads the same
local field jets and original transition jets, with no maxima over charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private theorem repairFieldPrefix_bound (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    {k j : ℕ} (hkj : k ≤ j) : A k ≤ bufferedTransitionPrefix A j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hA l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold 𝓘(ℝ,E) ∞ Y]

theorem repair_local_field_observer_smooth
    (owner observer : OpenPartialHomeomorph Y E)
    (hOwner : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (hObserver : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (field : Y → F) (localField : E → F) (U : Set Y) (W : Set E)
    (hU : IsOpen U) (hField : ∀ y ∈ U, field y = localField (owner y))
    (hDomain : U ⊆ owner.source ∩ owner ⁻¹' W)
    (hLocal : ContDiffOn ℝ ∞ localField W) :
    ContDiffOn ℝ ∞ (field ∘ observer.symm) (observer.target ∩ observer.symm ⁻¹' U) := by
  have hTrans : ContDiffOn ℝ ∞ (owner ∘ observer.symm)
      (observer.target ∩ observer.symm ⁻¹' U) :=
    (((contMDiffOn_of_mem_maximalAtlas hOwner).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hObserver).mono inter_subset_left)
      (fun _ hy => (hDomain hy.2).1)).contDiffOn)
  apply (hLocal.comp hTrans (fun _ hy => (hDomain hy.2).2)).congr
  intro y hy
  exact hField _ hy.2

theorem repair_local_field_observer_jet
    (owner observer : OpenPartialHomeomorph Y E)
    (hOwner : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (hObserver : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (field : Y → F) (localField : E → F) (U : Set Y) (W : Set E)
    (hU : IsOpen U) (hW : IsOpen W)
    (hField : ∀ y ∈ U, field y = localField (owner y))
    (hDomain : U ⊆ owner.source ∩ owner ⁻¹' W)
    (hLocal : ContDiffOn ℝ ∞ localField W)
    (Native Transition : ℕ → ℝ)
    (hNative : ∀ j, 0 ≤ Native j) (hTransition : ∀ j, 0 ≤ Transition j)
    (z : E) (hz : z ∈ observer.target) (hzU : observer.symm z ∈ U)
    (hLocalJets : ∀ k, ‖iteratedFDeriv ℝ k localField (owner (observer.symm z))‖ ≤ Native k)
    (hTransitionJets : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (owner ∘ observer.symm) z‖ ≤ Transition k)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (field ∘ observer.symm) z‖ ≤
      repairEntranceCompositionProfile Native Transition j := by
  let O := observer.target ∩ observer.symm ⁻¹' U
  have hO : IsOpen O := observer.symm.isOpen_inter_preimage hU
  have hzO : z ∈ O := ⟨hz,hzU⟩
  have ht : ContDiffOn ℝ ∞ (owner ∘ observer.symm) O :=
    (((contMDiffOn_of_mem_maximalAtlas hOwner).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hObserver).mono inter_subset_left)
      (fun _ hy => (hDomain hy.2).1)).contDiffOn)
  have heq : field ∘ observer.symm =ᶠ[𝓝 z] localField ∘ (owner ∘ observer.symm) := by
    filter_upwards [hO.mem_nhds hzO] with y hy
    exact hField _ hy.2
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
  have h := actual_fast_joint_chart_transfer Transition hTransition j (owner ∘ observer.symm)
    localField O W hO hW ht hLocal (fun _ hy => (hDomain hy.2).2) z hzO
    1 1 (bufferedTransitionPrefix Native j) zero_lt_one le_rfl (by
      intro k hk
      simp only [one_pow,one_mul]
      exact (hLocalJets k).trans (repairFieldPrefix_bound Native hNative hk)) (by
      intro k hk _
      simpa only [one_pow,one_mul] using hTransitionJets k hk)
  simpa only [one_pow,one_mul,repairEntranceCompositionProfile] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_local_field_observer_jet
