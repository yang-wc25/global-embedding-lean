import Upgrade.IncidenceAtlasTransition
import Upgrade.CompactScaleSelection
import GlobalEmbedding.Offline.UniformDiagonalSeparation

/-!
# The original C² budget preserves the already constructed diagonal separation

This applies the accepted uniform diagonal-separation theorem unchanged.
The new work is its actual finite-atlas consumer: the previous module's
transition-derivative bound converts the original probe C² norm to each of
the theorem's fixed centered-chart derivative tolerances. No new local
injectivity argument or replacement norm is used.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [CompactSpace M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- One tolerance in the original atlas C² norm preserves one fixed open
symmetric diagonal neighborhood for all later maps. The distant pair set is
compact and contains every cross-component pair not covered by this local
neighborhood. Empty sources are included by the accepted finite-cover proof. -/
theorem exists_originalC2_uniform_diagonal_separation
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ p : M, ∃ i, p ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ p, Function.Injective (mfderiv IM 𝓘(ℝ, V) F p)) :
    ∃ delta > 0, ∃ D : Set (M × M), IsOpen D ∧ Set.diagonal M ⊆ D ∧
      (∀ x y, (x, y) ∈ D → (y, x) ∈ D) ∧ IsCompact Dᶜ ∧
      (∀ z ∈ Dᶜ, z.1 ≠ z.2) ∧
      ∀ G : M → V, ContMDiff IM 𝓘(ℝ, V) ∞ G →
        probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal delta →
        ∀ x y, (x, y) ∈ D → G x = G y → x = y := by
  classical
  obtain ⟨centers, radius, eps, D, hlocal, hD, hdiag, hsym, hcompact, hoff, hstable⟩ :=
    exists_uniform_diagonal_separation F hF himm
  have hplot (p : M) : ContMDiffOn 𝓘(ℝ, E) IM ∞ (extChartAt IM p).symm
      (interior (extChartAt IM p).target) := by
    intro z hz
    exact ((contMDiffWithinAt_extChartAt_symm_target p (interior_subset hz)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hz)).contMDiffWithinAt
  choose C hC hbound using fun p : M ↦
    exists_originalC2_compact_plot_derivative_bound (N := N) A hA hcover
      (extChartAt IM p).symm isOpen_interior (hplot p)
      (isCompact_closedBall (extChartAt IM p p) (radius p)) (hlocal p).2.2
  obtain ⟨delta, hdelta, hdeltale⟩ := finite_positive_common_lower_bound
    (fun p : centers ↦ eps p.1 / (2 * (C p.1 + 1)))
    (fun p ↦ div_pos (hlocal p.1).2.1 (by have hp := hC p.1; positivity))
  refine ⟨delta, hdelta, D, hD, hdiag, hsym, hcompact, hoff, ?_⟩
  intro G hG hclose
  apply hstable G hG
  intro p hp z hz
  have hactual := hbound p F G hF hG delta hdelta.le hclose z hz
  have hCp := hC p
  have hsmall := (le_div_iff₀ (by positivity : 0 < 2 * (C p + 1))).mp
    (hdeltale ⟨p, hp⟩)
  exact hactual.trans_lt (by nlinarith)

#print axioms exists_originalC2_uniform_diagonal_separation

end GlobalEmbedding.Upgrade
