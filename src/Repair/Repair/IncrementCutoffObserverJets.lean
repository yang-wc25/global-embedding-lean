import Repair.EntranceCompositionProfiles
import Smoothing.TensorTransferJets
import GlobalEmbedding.Offline.SquareCutoffNormalization

/-! All observer derivatives of the literal parent times refinement cutoff.
The transition is used only where the original parent is active; elsewhere
the genuine zero germ supplies every derivative. The explicit profile reads
only the corresponding finite derivative prefixes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

private theorem incrementCutoffPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℝ,E) ∞ Y]

theorem increment_physical_refinement_observer_jets
    (q e : OpenPartialHomeomorph Y E)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,E) ∞ Y)
    (theta rho : Y → ℝ) (phi : E → ℝ)
    (hTheta : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ theta)
    (hPhi : ContDiff ℝ ∞ phi)
    (hSupport : tsupport theta ⊆ q.source)
    (hLiteral : rho = fun y => theta y*phi (q y))
    (Parent Scalar Transition : ℕ → ℝ)
    (hParent : ∀ j, 0 ≤ Parent j) (hScalar : ∀ j, 0 ≤ Scalar j)
    (hTransition : ∀ j, 0 ≤ Transition j)
    (hScalarJets : ∀ j y, ‖iteratedFDeriv ℝ j phi y‖ ≤ Scalar j)
    (z : E) (hz : z ∈ e.target)
    (hParentJets : ∀ j, ‖iteratedFDeriv ℝ j (theta ∘ e.symm) z‖ ≤ Parent j)
    (hTransitionJets : e.symm z ∈ tsupport theta → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (q ∘ e.symm) z‖ ≤ Transition j)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (rho ∘ e.symm) z‖ ≤
      tensorProductJetConstant Parent (repairEntranceCompositionProfile Scalar Transition) j := by
  have hC : ∀ j, 0 ≤ repairEntranceCompositionProfile Scalar Transition j :=
    repairEntranceCompositionProfile_nonneg Scalar Transition hScalar hTransition
  have hBudget : 0 ≤ tensorProductJetConstant Parent (repairEntranceCompositionProfile Scalar Transition) j :=
    tensorProductJetConstant_nonneg hParent hC j
  by_cases hActive : e.symm z ∈ tsupport theta
  · let t := e.symm.trans q
    have htz : z ∈ t.source := ⟨hz,hSupport hActive⟩
    have ht : ContDiffOn ℝ ∞ t t.source :=
      ((contMDiffOn_of_mem_maximalAtlas hq).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono (fun _ h => h.1))
        (fun _ h => h.2)).contDiffOn
    have hThetaObs : ContDiffOn ℝ ∞ (theta ∘ e.symm) t.source :=
      ((hTheta.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn).mono (fun _ h => h.1)
    have hPhiObs : ContDiffOn ℝ ∞ (phi ∘ t) t.source := hPhi.comp_contDiffOn ht
    have hPhiJets (k : ℕ) : ‖iteratedFDeriv ℝ k (phi ∘ t) z‖ ≤
        repairEntranceCompositionProfile Scalar Transition k := by
      have hb := actual_fast_joint_chart_transfer Transition hTransition k t phi t.source univ
        t.open_source isOpen_univ ht hPhi.contDiffOn (fun _ _ => mem_univ _) z htz
        1 1 (bufferedTransitionPrefix Scalar k) zero_lt_one le_rfl (by
          intro l hl
          simp only [one_pow,one_mul]
          exact (hScalarJets l (t z)).trans (incrementCutoffPrefix_bound Scalar hScalar hl)) (by
          intro l hl hlk
          simp only [one_pow,one_mul]
          change ‖iteratedFDeriv ℝ l (q ∘ e.symm) z‖ ≤ Transition l
          exact hTransitionJets hActive l hl)
      simpa only [one_pow,one_mul,repairEntranceCompositionProfile] using hb
    have h := tensor_scalar_product_jet_le Parent (repairEntranceCompositionProfile Scalar Transition)
      hParent hC t.open_source hThetaObs hPhiObs htz j hParentJets hPhiJets
    have heq : rho ∘ e.symm = fun y => (theta ∘ e.symm) y*(phi ∘ t) y := by
      rw [hLiteral]
      rfl
    rw [heq]
    exact h
  · have hRhoSupport : tsupport rho ⊆ tsupport theta := by
      rw [hLiteral]
      exact tsupport_mul_subset_left
    rw [iteratedFDeriv_comp_eq_zero_off_tsupport rho e.symm z (e.symm.continuousAt hz)
      (fun h => hActive (hRhoSupport h)) j,norm_zero]
    exact hBudget

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_physical_refinement_observer_jets
