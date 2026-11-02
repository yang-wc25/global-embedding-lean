import FaithfulRepair.OriginalTensorFrames
import Repair.EntranceOriginalObserverJets

/-! Read the actual source-only transition jets from the existing original
product-transition primitive.  No independent frame or tensor bound enters.
The inclusion and projection have norm at most one even when the parameter
dimension is zero. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulRepair

section ProductProjection
variable {Ep Es : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]

/-- Inserting zero parameters and taking the source projection does not
increase any genuine derivative norm of the source transition. -/
theorem source_transition_jet_le_original_product
    (e : OpenPartialHomeomorph Es Es) (he : ContDiffOn ℝ ∞ e e.source)
    (y : Es) (hy : y ∈ e.source) (k : ℕ) :
    ‖iteratedFDeriv ℝ k e y‖ ≤
      ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod e) (0,y)‖ := by
  let S := (OpenPartialHomeomorph.refl Ep).prod e
  let L : Es →L[ℝ] Ep × Es := ContinuousLinearMap.inr ℝ Ep Es
  let P : Ep × Es →L[ℝ] Es := ContinuousLinearMap.snd ℝ Ep Es
  have hS : ContDiffOn ℝ ∞ S S.source := contDiffOn_id.prodMap he
  have hPS : ContDiffOn ℝ ∞ (P ∘ S) S.source := P.contDiff.comp_contDiffOn hS
  have hz : (0,y) ∈ S.source := ⟨mem_univ _,hy⟩
  have hp := P.norm_iteratedFDeriv_comp_left (hS.contDiffAt (S.open_source.mem_nhds hz))
    (n := k) (by simp)
  have hp' : ‖iteratedFDeriv ℝ k (P ∘ S) (0,y)‖ ≤ ‖iteratedFDeriv ℝ k S (0,y)‖ :=
    hp.trans (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ Ep Es))
  have hL : ‖L‖ ≤ (1:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [L]
  have hl : ‖L‖^k ≤ (1:ℝ) := pow_le_one₀ (norm_nonneg _) hL
  have hcomp := norm_iteratedFDeriv_comp_linear_local L (P ∘ S) S.source S.open_source hPS y hz k
  change ‖iteratedFDeriv ℝ k e y‖ ≤ _ at hcomp
  exact hcomp.trans ((mul_le_mul hp' hl (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans_eq (mul_one _))
end ProductProjection

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The existing original spatial budget supplies precisely the primitive
needed by the real tensor-frame finiteness theorem, with the same bound. -/
theorem repairOriginalTransitionBudgets_source
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (Parameter Spatial : ℕ → ℝ)
    (h : RepairOriginalTransitionBudgets D Parameter Spatial) :
    ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ Spatial k := by
  intro p i k hk y hy ho
  have he : ContDiffOn ℝ ∞ ((D.atlas.chart p).symm.trans (D.atlas.chart i))
      ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source :=
    (round3Parameter_partial_trans_smooth (D.atlas.chart p).symm (D.atlas.chart i)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem p))
      (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i))).contDiffOn
  exact (source_transition_jet_le_original_product (Ep := EuclideanSpace ℝ (Fin d))
    _ he y ho k).trans (h.spatial p i k hk (0,y) hy ⟨mem_univ _,ho⟩)

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.source_transition_jet_le_original_product
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.repairOriginalTransitionBudgets_source
