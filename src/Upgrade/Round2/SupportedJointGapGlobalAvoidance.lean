import Round2.SupportedJointGapAvoidance
import Upgrade.CompactSupportedJointCover
import Upgrade.CompactOriginalSupported
import Upgrade.CompactFiniteProbeAvoidance

/-!
# Global dimension-three supported-coincidence removal from full probes and gap

All actual geometric preparation, compact cover, no-new-incidence protection
and finite parameter selection are reused. The only replacement is the local
source estimate at genuine incidence zeros, which now follows from metric
splitting and gauge cancellation. The conclusion removes supported
coincidences; arbitrary supported kernels are allowed to remain.
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

/-- The exact current-map supported-coincidence bad set in n = 3 is removed
by one actual same-metric probe perturbation. The selected normal gap is the
only added estimate for the chosen identification; no spatial DQ is required. -/
theorem exists_supportedCoincidence_removal_from_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : n = 3) (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2)
    (hfull : ∀ z ∈ P, Function.Surjective (trueSecondForm F hF z.1)) :
    ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∀ (probe : ExactProbeFamily F hF A waves), ChosenProbeNormalGap probe →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, 0 < t ∧ t < probe.threshold ∧ ∃ u : ProbeParameters r,
        ‖u‖ < probe.radius ∧
        probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon ∧
        (∀ x, inducedMetric (I := IM) (probe.map t u) x = inducedMetric (I := IM) F x) ∧
        ∀ z ∈ P, ¬ (HasSupportedKernel
          (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z.1) ∧
            probe.map t u z.1 = probe.map t u z.2) := by
  classical
  obtain ⟨packets, index, inSupport, preparation, centers, r, waves, labels,
      hlabels, hcover, _⟩ :=
    exists_finite_supportedJoint_prepared_actualWave_list A hA hcoverA F hF himm hphase
      (by omega : 3 ≤ n) hN hP hdistinct hfull
  let U : Set (M × M) := ⋃ c : centers, (preparation c.1).neighborhood
  have hU : IsOpen U := isOpen_iUnion fun c ↦ (preparation c.1).neighborhood_open
  have hcoverU : ∀ z ∈ P, HasSupportedKernel (trueSecondForm F hF z.1) →
      F z.1 = F z.2 → z ∈ U := by
    intro z hz hs hcoin
    obtain ⟨c, hc, hzc⟩ := hcover z ⟨hz, hs, hcoin⟩
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hzc⟩
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨enoNew, henoNew, hnoNew⟩ := exists_originalC2_supportedCoincidence_exclusion
    A hA hcompact hsupportCover (by omega : 2 ≤ n) F hF himm hphase hP hU hfull hcoverU
  refine ⟨r, waves, ?_⟩
  intro probe control epsilon hepsilon
  apply exists_probe_parameter_avoiding_finite_regions probe P
    (fun c : centers ↦ (preparation c.1).neighborhood)
    (fun t u z ↦ HasSupportedKernel
      (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z.1) ∧
        probe.map t u z.1 = probe.map t u z.2) enoNew henoNew (epsilon := epsilon)
  · intro t _ _ u _ hsmall z hz hbad
    exact mem_iUnion.mp (hnoNew (probe.map t u) (probe.slice_smooth t u)
      hsmall z hz hbad.1 hbad.2)
  · intro c
    exact (preparation c.1).exists_parameter_ball_scale_supportedCoincidence_null_of_gap
      hcompact himm hn r waves (fun l ↦ labels (c, l))
      (fun _ _ h ↦ congrArg Prod.snd (labels.injective h))
      (fun l ↦ hlabels c l.1 l.2) probe control
  · exact hepsilon

#print axioms exists_supportedCoincidence_removal_from_gap_probes
end GlobalEmbedding.Upgrade
