import Upgrade.CompactFixedAtlasJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual compact chart overlaps for the original atlas norm

All coordinates here are the literal `Fin n → ℝ` coordinates in
`probeAtlasCj`.  The compact evaluation set is the image of the intersection
of two actual supports.  The open differentiation domain is the chart
overlap, and is kept separate from that compact set.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => Fin n → ℝ

/-- The actual transition from the `B` chart to the `A` chart, in the
paper's coordinate norms.  No coordinate change is declared isometric. -/
def atlasNormTransition (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : P → P :=
  fun z ↦ (EuclideanSpace.equiv (Fin n) ℝ)
    (A.chart i ((B.chart j).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))

/-- Open overlap used for differentiating the actual transition. -/
def atlasNormTransitionDomain (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : Set P :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹'
    ((B.chart j).symm.trans (A.chart i)).source

/-- Compact set of transition points at which both original atlas support
conditions hold.  Its boundary is retained. -/
def atlasNormOverlapSupport (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : Set P :=
  (EuclideanSpace.equiv (Fin n) ℝ) ''
    ((B.chart j) '' (B.support j ∩ A.support i))

omit [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem atlasNormTransitionDomain_isOpen
    (A B : BufferedAtlas M E) (i : Fin A.count) (j : Fin B.count) :
    IsOpen (atlasNormTransitionDomain A B i j) :=
  ((B.chart j).symm.trans (A.chart i)).open_source.preimage
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous

theorem atlasNormOverlapSupport_subset_domain
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count) :
    atlasNormOverlapSupport A B i j ⊆ atlasNormTransitionDomain A B i j := by
  rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  change (EuclideanSpace.equiv (Fin n) ℝ).symm
    ((EuclideanSpace.equiv (Fin n) ℝ) (B.chart j x)) ∈
      ((B.chart j).symm.trans (A.chart i)).source
  rw [ContinuousLinearEquiv.symm_apply_apply, OpenPartialHomeomorph.trans_source]
  exact ⟨(B.chart j).map_source (hB.support_subset j hx.1), by
    simpa only [mem_preimage, (B.chart j).left_inv (hB.support_subset j hx.1)]
      using hA.support_subset i hx.2⟩

theorem atlasNormOverlapSupport_isCompact [T2Space M]
    (A B : BufferedAtlas M E) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) (i : Fin A.count) (j : Fin B.count) :
    IsCompact (atlasNormOverlapSupport A B i j) := by
  apply IsCompact.image _ (EuclideanSpace.equiv (Fin n) ℝ).continuous
  exact ((hBc j).inter (hAc i)).image_of_continuousOn
    ((B.chart j).continuousOn.mono (fun x hx ↦ hB.support_subset j hx.1))

/-- Both source charts and their true inverses occur in the transition's
smoothness proof.  Smoothness is asserted only on the actual open overlap. -/
theorem atlasNormTransition_contDiffOn
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count) :
    ContDiffOn ℝ ∞ (atlasNormTransition A B i j)
      (atlasNormTransitionDomain A B i j) := by
  intro z hz
  change (EuclideanSpace.equiv (Fin n) ℝ).symm z ∈
    ((B.chart j).symm.trans (A.chart i)).source at hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hb := (contMDiffAt_symm_of_mem_maximalAtlas (hB.chart_mem j) hz.1).comp z
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt.contMDiffAt
  have ha := (contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hz.2).comp z hb
  exact ((EuclideanSpace.equiv (Fin n) ℝ).contDiff.contDiffAt.comp z
    ha.contDiffAt).contDiffWithinAt

/-- Compactness supplies one bound for both transition derivatives before
the ambient maps or their C² budget are chosen.  Empty overlaps are allowed. -/
theorem exists_atlasNormTransition_twoJet_bound [T2Space M]
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) (i : Fin A.count) (j : Fin B.count) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ z ∈ atlasNormOverlapSupport A B i j,
      ‖iteratedFDeriv ℝ 1 (atlasNormTransition A B i j) z‖ ≤ D ∧
      ‖iteratedFDeriv ℝ 2 (atlasNormTransition A B i j) z‖ ≤ D := by
  have hs := atlasNormTransition_contDiffOn A B hA hB i j
  have ho := atlasNormTransitionDomain_isOpen A B i j
  have hc := atlasNormOverlapSupport_isCompact A B hB hAc hBc i j
  have hsub := atlasNormOverlapSupport_subset_domain A B hA hB i j
  obtain ⟨C₁, hC₁⟩ := hc.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hs ho (k := 1) (by simp)).mono hsub)
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hs ho (k := 2) (by simp)).mono hsub)
  refine ⟨|C₁| + |C₂| + 1, by linarith [abs_nonneg C₁, abs_nonneg C₂], ?_⟩
  intro z hz
  constructor
  · exact (hC₁ z hz).trans (by linarith [le_abs_self C₁, abs_nonneg C₂])
  · exact (hC₂ z hz).trans (by linarith [le_abs_self C₂, abs_nonneg C₁])

end GlobalEmbedding.Upgrade
