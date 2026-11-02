import Round2.SupportedGapGlobalAvoidance
import Round2.SupportedJointGapGlobalAvoidance
import Round2.CompactGapProbeProvider
import Upgrade.CompactUpgradeBudget

/-!
# The gap-only actual second operation in the two dimension ranges

For n≥4 the same full probes eliminate supported kernels on the current
compact full-rank source region. For n=3 they eliminate only supported
coincidences on the current pair region. Both operations are actually called
here, with a freshly selected finite wave list and current-map probes.
Original C² reserves preserve full rank and phase, while exact metrics
preserve immersion. No second-stage geometric conclusion is a premise.

Both actual avoidance endpoints now use only the selected zeroth-order normal
gap. The n=3 endpoint uses the proved gauge cancellation at its actual incidence
zeros; the n≥4 endpoint uses parameter rank. The existing dimension split and
all original geometric protection statements remain unchanged.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
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

theorem exists_actual_supported_stage_of_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x))
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2)
    (hfirst : ∀ z ∈ P, z.1 ∈ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal epsilon ∧
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧
      (∀ x ∈ C, Function.Surjective (trueSecondForm G hG x)) ∧
      (∀ z ∈ P, HasSupportedKernel (trueSecondForm G hG z.1) → G z.1 ≠ G z.2) ∧
      (4 ≤ n → ∀ x ∈ C, ¬ HasSupportedKernel (trueSecondForm G hG x)) := by
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  have hcodim : n < N := by
    have h := upgrade_normal_codimension (by omega : 1 ≤ n) hN
    omega
  obtain ⟨efull, hefull, hfullProtect⟩ := exists_originalC2_sameMetric_fullRank_reserve
    A hA hcompact hsupportCover (by omega : 2 ≤ n) hcodim F hF himm hphase hC hfull
  obtain ⟨ephase, lam, margin, hephase, _, _, hphaseProtect⟩ :=
    exists_originalC2_phase_protection A hA hcompact hsupportCover (by omega : 2 ≤ n)
      F hF himm hphase
  let budget := min epsilon (min efull ephase)
  have hbudget : 0 < budget := lt_min hepsilon (lt_min hefull hephase)
  have hbfull : budget ≤ efull := (min_le_right _ _).trans (min_le_left _ _)
  have hbphase : budget ≤ ephase := (min_le_right _ _).trans (min_le_right _ _)
  have hoperation : ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal budget ∧
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ z ∈ P, HasSupportedKernel (trueSecondForm G hG z.1) → G z.1 ≠ G z.2) ∧
      (4 ≤ n → ∀ x ∈ C, ¬ HasSupportedKernel (trueSecondForm G hG x)) := by
    by_cases hthree : n = 3
    · obtain ⟨r, waves, hremove⟩ := exists_supportedCoincidence_removal_from_gap_probes
        A hA hcompact hcoverA F hF himm hphase hthree hN hP hdistinct
        (fun z hz ↦ hfull z.1 (hfirst z hz))
      obtain ⟨probe, ⟨control⟩⟩ := provider F hF himm hphase r waves
      obtain ⟨t, ht, htt, u, hu, hsmall, hmetric, havoid⟩ :=
        hremove probe control budget hbudget
      exact ⟨probe.map t u, probe.slice_smooth t u, hsmall, hmetric,
        fun z hz hs hc ↦ havoid z hz ⟨hs, hc⟩, fun hfour ↦ (by omega)⟩
    · have hfour : 4 ≤ n := by omega
      obtain ⟨r, waves, hremove⟩ := exists_supported_removal_from_gap_probes
        A hA hcompact hcoverA F hF himm hphase hfour hN hC hfull
      obtain ⟨probe, ⟨control⟩⟩ := provider F hF himm hphase r waves
      obtain ⟨t, ht, htt, u, hu, hsmall, hmetric, havoid⟩ :=
        hremove probe control budget hbudget
      exact ⟨probe.map t u, probe.slice_smooth t u, hsmall, hmetric,
        fun z hz hs ↦ (havoid z.1 (hfirst z hz) hs).elim, fun _ ↦ havoid⟩
  obtain ⟨G, hG, hsmall, hmetric, havoid, hfour⟩ := hoperation
  exact ⟨G, hG, hsmall.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)), hmetric,
    fun x ↦ immersion_of_inducedMetric_eq F G x (hmetric x) (himm x),
    (hphaseProtect G hG (hsmall.trans (ENNReal.ofReal_le_ofReal hbphase))).1,
    hfullProtect G hG hmetric (hsmall.trans (ENNReal.ofReal_le_ofReal hbfull)), havoid, hfour⟩

end GlobalEmbedding.Upgrade
