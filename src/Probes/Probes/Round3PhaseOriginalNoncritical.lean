import Probes.Round3PhaseCompactPreparation
import Probes.ActualIncrementAdaptedPhaseReserve
import Probes.ActualOriginalSignedPhaseGood
import Probes.ActualIncrementOriginalSignedPhaseJets

/-! The original manifold phase differential, transported through the actual
original chart, supplies the native spatial noncriticality needed by the
constructed adapted refinement. No independent native margin is an input. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_actual_host_phase_spatial_ne_zero
    (c : OpenPartialHomeomorph M D)
    (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (psi : Ep × M → ℝ) (z : Ep × D) (hz : z.2 ∈ c.target)
    (hnative : DifferentiableAt ℝ (fun w : Ep × D => psi (w.1,c.symm w.2)) z)
    (hnonzero : (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (z.1,c.symm z.2))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) (c.symm z.2)) ≠ 0) :
    (fderiv ℝ (fun w : Ep × D => psi (w.1,c.symm w.2)) z).comp
      (ContinuousLinearMap.inr ℝ Ep D) ≠ 0 := by
  let f : M → ℝ := fun x => psi (z.1,x)
  have hf : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) f (c.symm z.2) := by
    by_contra h
    apply hnonzero
    change (tangentSpaceCastModel 𝓘(ℝ,ℝ) (f (c.symm z.2))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) f (c.symm z.2)) = 0
    rw [mfderiv_zero_of_not_mdifferentiableAt h, ContinuousLinearMap.comp_zero]
  have hc' := (actual_increment_maximal_chart_mdifferentiable c hc).mdifferentiableAt_symm hz
  have hm := mfderiv_comp z.2 hf hc'
  rw [mfderiv_eq_fderiv] at hm
  have hp : fderiv ℝ (f ∘ c.symm) z.2 =
      (fderiv ℝ (fun w : Ep × D => psi (w.1,c.symm w.2)) z).comp
        (ContinuousLinearMap.inr ℝ Ep D) := by
    have hn : HasFDerivAt (fun w : Ep × D => psi (w.1,c.symm w.2))
        (fderiv ℝ (fun w : Ep × D => psi (w.1,c.symm w.2)) z) (z.1,z.2) :=
      hnative.hasFDerivAt
    exact (hn.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv
  intro hzero
  have hpartial : fderiv ℝ (f ∘ c.symm) z.2 = 0 := hp.trans hzero
  rw [hpartial] at hm
  apply hnonzero
  ext v
  obtain ⟨u,hu⟩ := (actualIncrementChartDerivativeEquiv c hc z.2 hz).surjective v
  have he := congrArg (fun L => L u) hm
  change 0 = mfderiv 𝓙 𝓘(ℝ,ℝ) f (c.symm z.2)
    (actualIncrementChartDerivativeEquiv c hc z.2 hz u) at he
  rw [hu] at he
  exact he.symm

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_actual_host_phase_spatial_ne_zero
