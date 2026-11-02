import Upgrade.CompactValueGlobalAvoidance
import Upgrade.CompactProtectedAssembly
import Upgrade.CompactUpgradeBudget
import Round2.CompactGapProbeProvider

/-!
# The final actual value operation for the gap-only provider

This selects the final actual wave list and a full probe family only after
the earlier operations have produced the current map and recomputed its
remaining coincidence set. Original C² control preserves both previously
established value gaps and the chosen diagonal separation. If the protected
open sets cover the source, the current map is already an embedding and the
last probes call is skipped. Supported kernels may survive inside the second
protected neighborhood, as required in dimension three.

The existing protected-region argument is reused verbatim apart from the
provider type. This last value-only operation consumes no normal gap or DQ
field; it requires only the actual full probe family supplied by the provider.
-/

noncomputable section
open Set Bundle Manifold Module Topology GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [CompactSpace M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_embedding_from_current_protected_regions_of_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {D : Set (M × M)} (hP : IsCompact Dᶜ) (hdistinct : ∀ z ∈ Dᶜ, z.1 ≠ z.2)
    {O S : Set M} (hO : IsOpen O) (hS : IsOpen S)
    {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hgapO : ∀ z ∈ Dᶜ, z.1 ∈ closure O ∨ z.2 ∈ closure O → d < ‖F z.1 - F z.2‖)
    (hgapS : ∀ z ∈ Dᶜ, z.1 ∈ closure S ∨ z.2 ∈ closure S → e < ‖F z.1 - F z.2‖)
    (hremaining : ∀ z ∈ remainingPairRegion Dᶜ O S, F z.1 = F z.2 →
      Function.Surjective (trueSecondForm F hF z.1) ∧
        ¬ HasSupportedKernel (trueSecondForm F hF z.1))
    (delta : ℝ) (hdelta : 0 < delta)
    (hdiagonal : ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal delta →
      ∀ x y, (x, y) ∈ D → G x = G y → x = y)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal epsilon ∧
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G := by
  classical
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  by_cases hcovered : O ∪ S = univ
  · have hzero := probeAtlasC2_self_le_zero A hA F hF
    have hlocal := hdiagonal F hF (hzero.trans bot_le)
    have hemb := isClosedEmbedding_of_protected_cover hF.continuous hlocal hd he
      (fun z hz ho ↦ (hgapO z hz ho).le) (fun z hz hs ↦ (hgapS z hz hs).le) hcovered
    exact ⟨F, hF, hzero.trans bot_le, fun _ ↦ rfl, himm, hphase, hemb⟩
  · obtain ⟨egapO, hegapO, hprotectO⟩ :=
      exists_probeAtlasC2_protected_gap_budget A hA hsupportCover hd hgapO
    obtain ⟨egapS, hegapS, hprotectS⟩ :=
      exists_probeAtlasC2_protected_gap_budget A hA hsupportCover he hgapS
    obtain ⟨ephase, lam, margin, hephase, _, _, hprotectPhase⟩ :=
      exists_originalC2_phase_protection A hA hcompact hsupportCover (by omega : 2 ≤ n)
        F hF himm hphase
    let budget := min epsilon (min delta (min ephase (min egapO egapS)))
    have hbudget : 0 < budget :=
      lt_min hepsilon (lt_min hdelta (lt_min hephase (lt_min hegapO hegapS)))
    have hbE : budget ≤ epsilon := min_le_left _ _
    have hbD : budget ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
    have hbP : budget ≤ ephase :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hbO : budget ≤ egapO :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hbS : budget ≤ egapS :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨r, waves, hremove⟩ := exists_remaining_value_removal_from_probes
      A hA hcompact hcoverA F hF himm hphase hn hN
      (isCompact_remainingPairRegion hP hO hS)
      (fun z hz ↦ hdistinct z hz.1) hremaining
    obtain ⟨probe, _⟩ := provider F hF himm hphase r waves
    obtain ⟨t, ht, htt, u, hu, hsmall, hmetric, havoid⟩ := hremove probe budget hbudget
    let G := probe.map t u
    have hG := probe.slice_smooth t u
    have hlocal := hdiagonal G hG (hsmall.trans (ENNReal.ofReal_le_ofReal hbD))
    have hgapOG := hprotectO G (hsmall.trans (ENNReal.ofReal_le_ofReal hbO))
    have hgapSG := hprotectS G (hsmall.trans (ENNReal.ofReal_le_ofReal hbS))
    have hemb := isClosedEmbedding_of_remainingPairRegion_avoidance hG.continuous hlocal
      (half_pos hd) (half_pos he) hgapOG hgapSG havoid
    exact ⟨G, hG, hsmall.trans (ENNReal.ofReal_le_ofReal hbE), hmetric,
      fun x ↦ immersion_of_inducedMetric_eq F G x (hmetric x) (himm x),
      (hprotectPhase G hG (hsmall.trans (ENNReal.ofReal_le_ofReal hbP))).1, hemb⟩

end GlobalEmbedding.Upgrade
