import Upgrade.CompactRankQPreparedCover
import Upgrade.CompactOriginalRankCoincidence
import Upgrade.CompactFiniteProbeAvoidance
import Round2.RankQGapAvoidance

/-!
# Actual global rank-q coincidence removal with only zeroth-order Q gap

The old actual phase condition supplies the rank lower bound, so every old
rank≤q coincidence belongs to the compact rank=q set used for finite wave
preparation. The new local zero dictionary also handles rank≤q, using its
actual invertible q-block. Original-C² control excludes all new incidences
outside the fixed cover. The source-rank input is now proved only at the actual incidence zeros,
using gauge cancellation and the retained moving-tangent correction.
Thus the finite full-probes operation removes every
actual low-rank coincidence, without imposing its desired joint rank or
choosing a new cover after the returned weights.
-/

noncomputable section
open Set Filter Bundle Manifold Module MeasureTheory GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [LocallyCompactSpace M] [RegularSpace M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_rankQCoincidence_removal_from_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves), ChosenProbeNormalGap probe →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        ∀ z ∈ P, ¬ (finrank ℝ
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z.1).range ≤ n * (n - 1) / 2 ∧
            probe.map t u z.1 = probe.map t u z.2) := by
  classical
  obtain ⟨packets, index, inSupport, preparation, centers, r, waves, labels,
      hlabels, hcover, _⟩ :=
    exists_finite_rankQ_prepared_actualWave_list A hA hcoverA F hF himm hphase
      hn hN hP hdistinct
  let U : Set (M × M) := ⋃ c : centers, (preparation c.1).neighborhood
  have hU : IsOpen U := isOpen_iUnion fun c ↦ (preparation c.1).neighborhood_open
  have hcoverU : ∀ z ∈ P, finrank ℝ (trueSecondForm F hF z.1).range ≤ n * (n - 1) / 2 →
      F z.1 = F z.2 → z ∈ U := by
    intro z hz hr hcoin
    have heq := le_antisymm hr (phaseRegular_trueSecondForm_rank_lower F hF hphase z.1)
    obtain ⟨c, hc, hzc⟩ := hcover z ⟨hz, heq, hcoin⟩
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hzc⟩
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨enoNew, henoNew, hnoNew⟩ := exists_originalC2_rankCoincidence_exclusion
    A hA hcompact hsupportCover (by omega : 2 ≤ n) F hF himm hphase
      (n * (n - 1) / 2) hP hU hcoverU
  refine ⟨r, waves, ?_⟩
  intro probe control epsilon hepsilon
  apply exists_probe_parameter_avoiding_finite_regions probe P
    (fun c : centers ↦ (preparation c.1).neighborhood)
    (fun t u z ↦ finrank ℝ
      (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z.1).range ≤ n * (n - 1) / 2 ∧
        probe.map t u z.1 = probe.map t u z.2) enoNew henoNew (epsilon := epsilon)
  · intro t _ _ u _ hsmall z hz hbad
    exact mem_iUnion.mp (hnoNew (probe.map t u) (probe.slice_smooth t u)
      hsmall z hz hbad.1 hbad.2)
  · intro c
    exact (preparation c.1).exists_parameter_ball_scale_rankQCoincidence_null_of_gap hcompact himm
      c.1.2.2.1 probe control (fun l ↦ labels (c, l))
      (fun _ _ h ↦ congrArg Prod.snd (labels.injective h))
      (fun l ↦ hlabels c l.1 l.2)
  · exact hepsilon

end GlobalEmbedding.Upgrade
