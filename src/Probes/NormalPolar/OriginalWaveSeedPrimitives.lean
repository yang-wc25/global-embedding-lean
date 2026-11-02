import NormalPolar.OriginalWaveSeedBuffers

/-!
# Raw cutoff, normal and reference profiles of the actual original wave pieces

The fields here are defined by the literal original wave and its constructed
adapted chart. Smoothness and support are conclusions. Compact target buffers
then produce all-order raw jet constants before any scale is supplied. These
are primitive input profiles, not estimates postulated for the finite solver.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter
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

namespace OriginalWaveSeedRefinement

def cutoffCoordinates (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : Z × EuclideanSpace ℝ (Fin (m+1)) → ℝ :=
  d.cutoff i ∘ (d.chart i).symm

def normalCoordinates (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : Z × EuclideanSpace ℝ (Fin (m+1)) → EuclideanSpace ℝ (Fin N) :=
  fun z => (w.normal ((d.chart i).symm z).2 : EuclideanSpace ℝ (Fin N))

def referenceCoordinates (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : Z × EuclideanSpace ℝ (Fin (m+1)) → EuclideanSpace ℝ (Fin N) :=
  fun z => F ((d.chart i).symm z).2

theorem cutoffCoordinates_smooth (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) :
    ContDiffOn ℝ ∞ (d.cutoffCoordinates i) (d.chart i).target :=
  ((d.cutoff_smooth i).comp_contMDiffOn (d.inverse_smooth i)).contDiffOn

theorem normalCoordinates_smooth (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) :
    ContDiffOn ℝ ∞ (d.normalCoordinates i) (d.chart i).target := by
  have hmap : MapsTo (fun z : Z × EuclideanSpace ℝ (Fin (m+1)) =>
      ((d.chart i).symm z).2) (d.chart i).target w.domain := by
    intro z hz
    exact (d.chart_source i ((d.chart i).map_target hz)).2
  exact (w.normal_smooth.comp
    (contMDiff_snd.comp_contMDiffOn (d.inverse_smooth i)) hmap).contDiffOn

theorem referenceCoordinates_smooth (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) :
    ContDiffOn ℝ ∞ (d.referenceCoordinates i) (d.chart i).target :=
  (hF.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn (d.inverse_smooth i))).contDiffOn

/-- The raw coordinate cutoff has no additional carrier hypothesis. -/
theorem cutoffCoordinates_support (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) (z : Z × EuclideanSpace ℝ (Fin (m+1)))
    (hz : z ∈ (d.chart i).target) (hcut : z ∈ tsupport (d.cutoffCoordinates i)) :
    (d.chart i).symm z ∈ tsupport (d.cutoff i) := by
  by_contra hn
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    ((d.chart i).symm.continuousAt hz)
  exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hcut

theorem primitive_amplitude (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) (z : Z × M) (hz : z ∈ (d.chart i).source) :
    d.cutoffCoordinates i (d.chart i z) • d.normalCoordinates i (d.chart i z) =
      d.cutoff i z • (w.normal z.2 : EuclideanSpace ℝ (Fin N)) := by
  change d.cutoff i ((d.chart i).symm (d.chart i z)) •
      (w.normal ((d.chart i).symm (d.chart i z)).2 : EuclideanSpace ℝ (Fin N)) = _
  rw [(d.chart i).left_inv hz]

/-- Three actual primitive profiles, chosen independently of every later scale.
All whole-chart target points and every derivative order are included. -/
theorem exists_primitive_profiles
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) (b : OriginalWaveSeedBuffer d i) :
    ∃ Cchi Cnu CF : ℕ → ℝ,
      (∀ j, 0 < Cchi j ∧ 0 < Cnu j ∧ 0 < CF j) ∧
      ∀ ell : ℝ, 0 ≤ ell → ell ≤ 1 → ∀ j z, z ∈ b.chart.target →
        ell^j * ‖iteratedFDeriv ℝ j (d.cutoffCoordinates i) z‖ ≤ Cchi j ∧
        ell^j * ‖iteratedFDeriv ℝ j (d.normalCoordinates i) z‖ ≤ Cnu j ∧
        ell^j * ‖iteratedFDeriv ℝ j (d.referenceCoordinates i) z‖ ≤ CF j := by
  obtain ⟨Cchi,hchi,bchi⟩ := b.exists_raw_profile _ (d.cutoffCoordinates_smooth i)
  obtain ⟨Cnu,hnu,bnu⟩ := b.exists_raw_profile _ (d.normalCoordinates_smooth i)
  obtain ⟨CF,hF,bF⟩ := b.exists_raw_profile _ (d.referenceCoordinates_smooth i)
  exact ⟨Cchi,Cnu,CF,fun j => ⟨hchi j,hnu j,hF j⟩,
    fun ell he he1 j z hz => ⟨bchi ell he he1 j z hz,bnu ell he he1 j z hz,
      bF ell he he1 j z hz⟩⟩

end OriginalWaveSeedRefinement
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.cutoffCoordinates_support
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.exists_primitive_profiles
