import Upgrade.CompactSupportedCover
import Upgrade.CompactOriginalSupported
import Upgrade.CompactFiniteProbeAvoidance
import Upgrade.CompactFullRankProtection
import Round2.SupportedGapPreparedScale

/-!
# Actual n≥4 supported-kernel removal with only the selected normal gap

The actual finite wave list, prepared neighborhoods, supported rank, original
C² no-new-incidence theorem and finite null-union selection are reused.  The
only change to the prior global endpoint is that its normal-control input now
contains the actual zeroth-order gap alone.  This branch never needed spatial
DQ to supply its parameter incidence rank.  Neither the full probes nor the
selected gap is constructed here.
-/

noncomputable section
open Set Filter Bundle Manifold Module MeasureTheory GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- One actual finite wave list removes all supported kernels on the current
compact full-rank region.  The fixed parameter ball and scale are obtained from
full probes and the zero-order normal gap; no spatial DQ hypothesis appears.
The conclusion is deliberately restricted to n≥4. -/
theorem exists_supported_removal_from_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 4 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x)) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves), ChosenProbeNormalGap probe →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        ∀ x ∈ C, ¬ HasSupportedKernel
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) x) := by
  classical
  obtain ⟨partners, packets, index, inSupport, preparation, centers, r, waves, labels,
      hlabels, hcover, _⟩ :=
    exists_finite_supported_prepared_actualWave_list A hA hcoverA F hF himm hphase
      (by omega : 3 ≤ n) hN hC hfull
  let U : Set M := ⋃ c : centers, (preparation c.1).neighborhood
  have hU : IsOpen U := isOpen_iUnion fun c ↦ (preparation c.1).neighborhood_open
  have hcoverU : ∀ x ∈ C, HasSupportedKernel (trueSecondForm F hF x) → x ∈ U := by
    intro x hx hs
    obtain ⟨c, hc, hxc⟩ := hcover x ⟨hx, hs⟩
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨enoNew, henoNew, hnoNew⟩ := exists_originalC2_supported_exclusion
    A hA hcompact hsupportCover (by omega : 2 ≤ n) F hF himm hphase hC hU hfull hcoverU
  refine ⟨r, waves, ?_⟩
  intro probe control epsilon hepsilon
  apply exists_probe_parameter_avoiding_finite_regions probe C
    (fun c : centers ↦ (preparation c.1).neighborhood)
    (fun t u x ↦ HasSupportedKernel
      (trueSecondForm (probe.map t u) (probe.slice_smooth t u) x))
    enoNew henoNew (epsilon := epsilon)
  · intro t _ _ u _ hsmall x hx hs
    exact mem_iUnion.mp ((hnoNew (probe.map t u) (probe.slice_smooth t u) hsmall).2 x hx hs)
  · intro c
    exact (preparation c.1).exists_parameter_ball_scale_supported_null_of_gap hcompact hn
      r waves (fun l ↦ labels (c, l, 0)) (fun l ↦ hlabels c l 0) probe control
  · exact hepsilon

/-- The same operation retains the current actual phase margin and full rank
on the compact region, with a strict finite original C² budget.  These facts
come from the proved original-metric and original-C² protection lemmas, not
from additional fields of the probes or gap record. -/
theorem exists_supported_removal_preserving_geometry_from_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 4 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x)) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves), ChosenProbeNormalGap probe →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≠ ⊤ ∧
        (probeAtlasCj A 2 (probe.map t u - F)).toReal < epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (probe.map t u) x)) ∧
        PhaseRegular (probe.map t u) (probe.slice_smooth t u) ∧
        ∀ x ∈ C, Function.Surjective
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) x) ∧
          ¬ HasSupportedKernel (trueSecondForm (probe.map t u) (probe.slice_smooth t u) x) := by
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  have hprod : n * (n + 1) = n * (n - 1) + 2 * n := by
    calc
      n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
      _ = n * (n - 1) + 2 * n := by ring
  have hcodim : n < N := by omega
  obtain ⟨efull, hefull, hfullProtect⟩ := exists_originalC2_sameMetric_fullRank_reserve
    A hA hcompact hsupportCover (by omega : 2 ≤ n) hcodim F hF himm hphase hC hfull
  obtain ⟨ephase, lam, margin, hephase, _, _, hphaseProtect⟩ :=
    exists_originalC2_phase_protection A hA hcompact hsupportCover (by omega : 2 ≤ n)
      F hF himm hphase
  obtain ⟨r, waves, hremove⟩ := exists_supported_removal_from_gap_probes
    A hA hcompact hcoverA F hF himm hphase hn hN hC hfull
  refine ⟨r, waves, ?_⟩
  intro probe control epsilon hepsilon
  let e := min (epsilon / 2) (min efull ephase)
  have he : 0 < e := lt_min (half_pos hepsilon) (lt_min hefull hephase)
  obtain ⟨t, ht, htt, u, hu, hsmall, hmetric, hnonsupported⟩ := hremove probe control e he
  have hsmallFull : probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal efull :=
    hsmall.trans (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallPhase : probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal ephase :=
    hsmall.trans (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _)))
  have hfinite : probeAtlasCj A 2 (probe.map t u - F) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hreal : (probeAtlasCj A 2 (probe.map t u - F)).toReal < epsilon := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
    rw [ENNReal.toReal_ofReal he.le] at h
    exact h.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hepsilon))
  exact ⟨t, ht, htt, u, hu, hfinite, hreal, hmetric,
    fun x ↦ immersion_of_inducedMetric_eq F (probe.map t u) x (hmetric x) (himm x),
    (hphaseProtect (probe.map t u) (probe.slice_smooth t u) hsmallPhase).1,
    fun x hx ↦ ⟨hfullProtect (probe.map t u) (probe.slice_smooth t u) hmetric hsmallFull x hx,
      hnonsupported x hx⟩⟩

end GlobalEmbedding.Upgrade
