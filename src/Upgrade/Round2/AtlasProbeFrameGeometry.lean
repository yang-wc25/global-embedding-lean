import Upgrade.SupportedProbeAtlasTransport
import GlobalEmbedding.Paper.SymmetricSquareMapNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual change of the source frame used by full probes

The frame ratio is the derivative of the real chart transition.  We never
assume continuity of a field of native manifold differentials whose native
chart can change with the point.  The continuous object used for compact
bounds is the derivative of this fixed Euclidean chart transition.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal transition from B coordinates to A coordinates. -/
def atlasProbeTransition (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : E → E :=
  (A.chart i) ∘ (B.chart j).symm

/-- The open differentiation domain of that same transition. -/
def atlasProbeTransitionDomain (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : Set E :=
  ((B.chart j).symm.trans (A.chart i)).source

/-- The full compact support overlap, including its boundary. -/
def atlasProbeOverlapSupport (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) : Set E :=
  (B.chart j) '' (B.support j ∩ A.support i)

theorem atlasProbeTransitionDomain_isOpen
    (A B : BufferedAtlas M E) (i : Fin A.count) (j : Fin B.count) :
    IsOpen (atlasProbeTransitionDomain A B i j) :=
  ((B.chart j).symm.trans (A.chart i)).open_source

theorem atlasProbeOverlapSupport_subset_domain
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count) :
    atlasProbeOverlapSupport A B i j ⊆ atlasProbeTransitionDomain A B i j := by
  rintro s ⟨z, hz, rfl⟩
  rw [atlasProbeTransitionDomain, OpenPartialHomeomorph.trans_source]
  exact ⟨(B.chart j).map_source (hB.support_subset j hz.1), by
    simpa only [mem_preimage, (B.chart j).left_inv (hB.support_subset j hz.1)]
      using hA.support_subset i hz.2⟩

theorem atlasProbeOverlapSupport_isCompact [T2Space M]
    (A B : BufferedAtlas M E) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) (i : Fin A.count) (j : Fin B.count) :
    IsCompact (atlasProbeOverlapSupport A B i j) :=
  ((hBc j).inter (hAc i)).image_of_continuousOn
    ((B.chart j).continuousOn.mono (fun z hz ↦ hB.support_subset j hz.1))

theorem atlasProbeTransition_contDiffOn
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count) :
    ContDiffOn ℝ ∞ (atlasProbeTransition A B i j)
      (atlasProbeTransitionDomain A B i j) := by
  intro s hs
  change s ∈ ((B.chart j).symm.trans (A.chart i)).source at hs
  rw [OpenPartialHomeomorph.trans_source] at hs
  exact ((contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hs.2).comp s
    (contMDiffAt_symm_of_mem_maximalAtlas (hB.chart_mem j) hs.1)).contDiffAt.contDiffWithinAt

/-- Both sides are the actual inverse-chart differentials at the same source
point.  Native tangent chart choices cancel in their real transition ratio. -/
theorem probeAtlasFrame_change_atlas
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count)
    (z : M) (hzA : z ∈ (A.chart i).source) (hzB : z ∈ (B.chart j).source) :
    probeAtlasFrame B j z = (probeAtlasFrame A i z).comp
      (fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)) := by
  have hAd := (contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hzA).mdifferentiableAt
    (by simp)
  have hBd := (contMDiffAt_symm_of_mem_maximalAtlas (hB.chart_mem j)
    ((B.chart j).map_source hzB)).mdifferentiableAt (by simp)
  have hAd' : MDifferentiableAt IM IM (A.chart i) ((B.chart j).symm (B.chart j z)) := by
    simpa only [(B.chart j).left_inv hzB] using hAd
  have hc := mfderiv_comp (B.chart j z) hAd' hBd
  rw [mfderiv_eq_fderiv, (B.chart j).left_inv hzB] at hc
  have htransition : fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z) =
      (mfderiv IM IM (A.chart i) z).comp (probeAtlasFrame B j z) := hc
  rw [htransition]
  apply ContinuousLinearMap.ext
  intro v
  exact (((probeAtlasChart_mdifferentiable A hA i).mfderiv hzA).symm_apply_apply
    (probeAtlasFrame B j z v)).symm

/-- The actual transition operator on the paper's original symmetric-square
quotient.  It is independent of the map and of all probe parameters. -/
def atlasProbeTransitionSquare (A B : BufferedAtlas M E)
    (i : Fin A.count) (j : Fin B.count) (z : M) :
    SymmetricSquare E →L[ℝ] SymmetricSquare E :=
  LinearMap.toContinuousLinearMap (symmetricSquareLinearMap
    (fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)).toLinearMap)

theorem atlasProbeTransitionSquare_norm_le
    (A B : BufferedAtlas M E) (i : Fin A.count) (j : Fin B.count) (z : M) :
    ‖atlasProbeTransitionSquare A B i j z‖ ≤
      ‖fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro q
  change ‖symmetricSquareLinearMap
    (fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)).toLinearMap q‖ ≤ _
  rw [symmetric_square_linear_map_eq]
  exact symmetricSquareMap_norm_le _ q

/-- One real compact overlap has a fixed transition-derivative bound. -/
theorem exists_atlasProbeTransition_bound [T2Space M]
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) (i : Fin A.count) (j : Fin B.count) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ z ∈ B.support j ∩ A.support i,
      ‖fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)‖ ≤ D := by
  have hs := atlasProbeTransition_contDiffOn A B hA hB i j
  have ho := atlasProbeTransitionDomain_isOpen A B i j
  have hc := atlasProbeOverlapSupport_isCompact A B hB hAc hBc i j
  have hsub := atlasProbeOverlapSupport_subset_domain A B hA hB i j
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hs ho (k := 1) (by simp)).mono hsub)
  refine ⟨|C| + 1, by linarith [abs_nonneg C], ?_⟩
  intro z hz
  have h := hC (B.chart j z) ⟨z, hz, rfl⟩
  rw [norm_iteratedFDeriv_one] at h
  exact h.trans ((le_abs_self C).trans (by linarith))

/-- A single actual symmetric-square transport bound over every pair of
compact supports, chosen before any map, wave, parameter or scale. Empty
chart-pair types and empty overlaps are allowed. -/
theorem exists_uniform_atlasProbeTransitionSquare_bound [T2Space M]
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (i : Fin A.count) (j : Fin B.count) (z : M),
      z ∈ B.support j → z ∈ A.support i →
      ‖atlasProbeTransitionSquare A B i j z‖ ≤ R := by
  classical
  choose D hD hbound using exists_atlasProbeTransition_bound A B hA hB hAc hBc
  obtain ⟨Dmax, hDmax⟩ := Finite.exists_le (fun p : Fin A.count × Fin B.count ↦ D p.1 p.2)
  let Dtotal := |Dmax| + 1
  have htotal : 0 < Dtotal := by dsimp only [Dtotal]; positivity
  refine ⟨Dtotal ^ 2, sq_pos_of_pos htotal, ?_⟩
  intro i j z hzB hzA
  have hd : ‖fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)‖ ≤ Dtotal :=
    (hbound i j z ⟨hzB, hzA⟩).trans ((hDmax (i,j)).trans
      ((le_abs_self Dmax).trans (by dsimp only [Dtotal]; linarith)))
  exact (atlasProbeTransitionSquare_norm_le A B i j z).trans
    (pow_le_pow_left₀ (norm_nonneg _) hd 2)

#print axioms probeAtlasFrame_change_atlas
#print axioms atlasProbeTransitionSquare_norm_le
#print axioms exists_uniform_atlasProbeTransitionSquare_bound

end GlobalEmbedding.Upgrade
