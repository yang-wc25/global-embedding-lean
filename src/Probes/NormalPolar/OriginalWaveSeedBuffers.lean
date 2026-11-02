import NormalPolar.OriginalWaveSeedRefinement
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Genuine compact target buffers for the original adapted wave pieces

The finite partition is fixed before any scale. Each actual localized cutoff
has compact support because the original manifold and the one-point seed are
compact. Its image in its own adapted chart therefore admits a compact buffer
strictly inside the old target. Restricting the target preserves the literal
forward and inverse functions, phase identities and the whole cutoff support.
This supplies all-order raw chart bounds before the scale is chosen.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}

/-- An actual compact buffer, not a supplied bound on a reconstructed wave. -/
structure OriginalWaveSeedBuffer
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) where
  compactTarget : Set (Z × EuclideanSpace ℝ (Fin (m+1)))
  compact : IsCompact compactTarget
  contained : compactTarget ⊆ (d.chart i).target
  contains_support : (d.chart i) '' tsupport (d.cutoff i) ⊆ interior compactTarget

theorem exists_originalWaveSeedBuffer
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) :
    Nonempty (OriginalWaveSeedBuffer d i) := by
  have hK : IsCompact (tsupport (d.cutoff i)) := (isClosed_tsupport _).isCompact
  have hs : tsupport (d.cutoff i) ⊆ (d.chart i).source :=
    fun _ hx => (d.cutoff_support i hx).2
  have hi := hK.image_of_continuousOn ((d.chart i).continuousOn.mono hs)
  have ht : (d.chart i) '' tsupport (d.cutoff i) ⊆ (d.chart i).target := by
    rintro _ ⟨x,hx,rfl⟩
    exact (d.chart i).map_source (hs hx)
  obtain ⟨L,hL,hKL,hLT⟩ := exists_compact_between hi (d.chart i).open_target ht
  exact ⟨⟨L,hL,hLT,hKL⟩⟩

namespace OriginalWaveSeedBuffer

variable {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

/-- The restricted chart retains the exact old functions in both directions. -/
def chart (b : OriginalWaveSeedBuffer d i) :
    OpenPartialHomeomorph (Z × M) (Z × EuclideanSpace ℝ (Fin (m+1))) :=
  ((d.chart i).symm.restrOpen (interior b.compactTarget) isOpen_interior).symm

theorem chart_apply (b : OriginalWaveSeedBuffer d i) (z : Z × M) :
    b.chart z = d.chart i z := rfl

theorem inverse_apply (b : OriginalWaveSeedBuffer d i)
    (z : Z × EuclideanSpace ℝ (Fin (m+1))) :
    b.chart.symm z = (d.chart i).symm z := rfl

theorem chart_target (b : OriginalWaveSeedBuffer d i) :
    b.chart.target = interior b.compactTarget := by
  change (d.chart i).target ∩ interior b.compactTarget = interior b.compactTarget
  exact inter_eq_right.mpr (interior_subset.trans b.contained)

theorem chart_source_subset (b : OriginalWaveSeedBuffer d i) :
    b.chart.source ⊆ (d.chart i).source := fun _ hz => hz.1

theorem cutoff_support (b : OriginalWaveSeedBuffer d i) :
    tsupport (d.cutoff i) ⊆ b.chart.source := by
  intro z hz
  exact ⟨(d.cutoff_support i hz).2,b.contains_support ⟨z,hz,rfl⟩⟩

theorem target_closure_compact (b : OriginalWaveSeedBuffer d i) :
    IsCompact (closure b.chart.target) ∧ closure b.chart.target ⊆ (d.chart i).target := by
  have hs : closure b.chart.target ⊆ b.compactTarget := by
    rw [b.chart_target]
    exact closure_minimal interior_subset b.compact.isClosed
  exact ⟨b.compact.of_isClosed_subset isClosed_closure hs,hs.trans b.contained⟩

theorem chart_smooth (b : OriginalWaveSeedBuffer d i) :
    ContMDiffOn
      (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
      𝓘(ℝ,Z × EuclideanSpace ℝ (Fin (m+1))) ∞ b.chart b.chart.source :=
  (d.chart_smooth i).mono b.chart_source_subset

theorem inverse_smooth (b : OriginalWaveSeedBuffer d i) :
    ContMDiffOn 𝓘(ℝ,Z × EuclideanSpace ℝ (Fin (m+1)))
      (ModelWithCorners.prod 𝓘(ℝ,Z) 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
      ∞ b.chart.symm b.chart.target := by
  apply (d.inverse_smooth i).mono
  rw [b.chart_target]
  exact interior_subset.trans b.contained

theorem phase_coordinate (b : OriginalWaveSeedBuffer d i) (z : Z × M)
    (hz : z ∈ b.chart.source) :
    (b.chart z).1 = z.1 ∧ (b.chart z).2 0 = weight * w.phase z.2 :=
  d.phase_coordinate i z (b.chart_source_subset hz)

theorem inverse_phase (b : OriginalWaveSeedBuffer d i)
    (z : Z × EuclideanSpace ℝ (Fin (m+1))) (hz : z ∈ b.chart.target) :
    (b.chart.symm z).1 = z.1 ∧ weight * w.phase (b.chart.symm z).2 = z.2 0 := by
  apply d.inverse_phase i z
  exact (b.target_closure_compact.2) (subset_closure hz)

/-- Constants for a fixed primitive field are selected before every scale,
with all derivative orders retained on the whole new chart target. -/
theorem exists_raw_profile {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b : OriginalWaveSeedBuffer d i)
    (f : Z × EuclideanSpace ℝ (Fin (m+1)) → Y)
    (hf : ContDiffOn ℝ ∞ f (d.chart i).target) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ j z, z ∈ b.chart.target → ell^j * ‖iteratedFDeriv ℝ j f z‖ ≤ C j := by
  have hc (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j f) b.compactTarget := by
    intro z hz
    exact ((hf.contDiffAt ((d.chart i).open_target.mem_nhds (b.contained hz))).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  have hb (j : ℕ) : ∃ C : ℝ, ∀ z ∈ b.compactTarget, ‖iteratedFDeriv ℝ j f z‖ ≤ C :=
    b.compact.exists_bound_of_continuousOn (hc j)
  choose C hC using hb
  refine ⟨fun j => |C j|+1,fun j => by positivity,?_⟩
  intro ell hell hell1 j z hz
  have hzL : z ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz
  calc
    ell^j * ‖iteratedFDeriv ℝ j f z‖ ≤ 1 * ‖iteratedFDeriv ℝ j f z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
    _ ≤ C j := by simpa only [one_mul] using hC j z hzL
    _ ≤ |C j|+1 := (le_abs_self _).trans (by linarith)

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_originalWaveSeedBuffer
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_raw_profile
