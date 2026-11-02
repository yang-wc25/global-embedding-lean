import Upgrade.CompactValueCover
import Upgrade.CompactOriginalValueCoincidence
import Upgrade.CompactFiniteProbeAvoidance
import Upgrade.SupportedValuePreparedScale
import Upgrade.CompactFixedAtlasPhase
import GlobalEmbedding.Offline.CoincidenceAvoidanceEmbedding

/-!
# Actual global removal of the remaining value coincidences

The current compact coincidence set supplies a finite list of actual legal
waves, with the same unweighted value frame and spatial margins fixed before
the probes provider returns its weights. The actual per-prepared-region null
theorem is combined with original-C² exclusion of all newly created
coincidences outside that cover. A good parameter is selected in one positive
ball, at one positive scale. The global correction at both source points is
retained. No selected-normal identification estimate is needed for this last
value-only operation.

The full probes provider remains an explicit upstream dependency. This is an
operation in the upgrade chain, not an unconditional original upgrade claim.
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

theorem exists_remaining_value_removal_from_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2)
    (hremaining : ∀ z ∈ P, F z.1 = F z.2 →
      Function.Surjective (trueSecondForm F hF z.1) ∧
        ¬ HasSupportedKernel (trueSecondForm F hF z.1)) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves),
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        ∀ z ∈ P, probe.map t u z.1 ≠ probe.map t u z.2 := by
  classical
  obtain ⟨packets, index, inSupport, preparation, centers, r, waves, labels,
      hlabels, hcover, _⟩ :=
    exists_finite_value_prepared_actualWave_list A hA hcoverA F hF himm hphase
      hn hN hP hdistinct hremaining
  let U : Set (M × M) := ⋃ c : centers, (preparation c.1).neighborhood
  have hU : IsOpen U := isOpen_iUnion fun c ↦ (preparation c.1).neighborhood_open
  have hcoverU : ∀ z ∈ P, F z.1 = F z.2 → z ∈ U := by
    intro z hz hs
    obtain ⟨c, hc, hzc⟩ := hcover z ⟨hz, hs⟩
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hzc⟩
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨enoNew, henoNew, hnoNew⟩ := exists_originalC2_valueCoincidence_exclusion
    A hA hsupportCover F hF.continuous hP hU hcoverU
  refine ⟨r, waves, ?_⟩
  intro probe epsilon hepsilon
  apply exists_probe_parameter_avoiding_finite_regions probe P
    (fun c : centers ↦ (preparation c.1).neighborhood)
    (fun t u z ↦ probe.map t u z.1 = probe.map t u z.2) enoNew henoNew
    (epsilon := epsilon)
  · intro t _ _ u _ hsmall z hz hcoincidence
    exact mem_iUnion.mp (hnoNew (probe.map t u) hsmall z hz hcoincidence)
  · intro c
    exact (preparation c.1).exists_parameter_ball_scale_value_null hcompact hsupportCover
      (by omega : 2 ≤ n) himm hphase r waves
      (fun l ↦ labels (c, l, 0)) (fun l ↦ hlabels c l 0) probe
  · exact hepsilon

/-- The last value operation preserves the original phase condition and exact
metric, and hence immersion, with a strict finite original C² budget. -/
theorem exists_remaining_value_removal_preserving_geometry_from_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2)
    (hremaining : ∀ z ∈ P, F z.1 = F z.2 →
      Function.Surjective (trueSecondForm F hF z.1) ∧
        ¬ HasSupportedKernel (trueSecondForm F hF z.1)) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves),
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≠ ⊤ ∧
        (probeAtlasCj A 2 (probe.map t u - F)).toReal < epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (probe.map t u) x)) ∧
        PhaseRegular (probe.map t u) (probe.slice_smooth t u) ∧
        ∀ z ∈ P, probe.map t u z.1 ≠ probe.map t u z.2 := by
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨ephase, lam, margin, hephase, _, _, hphaseProtect⟩ :=
    exists_originalC2_phase_protection A hA hcompact hsupportCover (by omega : 2 ≤ n)
      F hF himm hphase
  obtain ⟨r, waves, hremove⟩ := exists_remaining_value_removal_from_probes A hA hcompact hcoverA
    F hF himm hphase hn hN hP hdistinct hremaining
  refine ⟨r, waves, ?_⟩
  intro probe epsilon hepsilon
  let e := min (epsilon / 2) ephase
  have he : 0 < e := lt_min (half_pos hepsilon) hephase
  obtain ⟨t, ht, htt, u, hu, hsmall, hmetric, havoid⟩ := hremove probe e he
  have hsmallPhase : probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal ephase :=
    hsmall.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hfinite : probeAtlasCj A 2 (probe.map t u - F) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hreal : (probeAtlasCj A 2 (probe.map t u - F)).toReal < epsilon := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
    rw [ENNReal.toReal_ofReal he.le] at h
    exact h.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hepsilon))
  exact ⟨t, ht, htt, u, hu, hfinite, hreal, hmetric,
    fun x ↦ immersion_of_inducedMetric_eq F (probe.map t u) x (hmetric x) (himm x),
    (hphaseProtect (probe.map t u) (probe.slice_smooth t u) hsmallPhase).1, havoid⟩

end GlobalEmbedding.Upgrade
