import Round2.AtlasProbeTransportProvider
import Round2.AtlasNormUpgradeEndpoint

/-!
# The original probes may choose their own atlas for each invocation

The remaining analytic provider may choose a compact smooth covering atlas
after receiving the current immersion and its actual finite legal wave list.
The constructed atlas transport then moves that SAME full probe family to
the one fixed native atlas used by the geometric upgrade. The supplied atlas
does not vary with t or u, and no incidence rank or embedding output is part
of the provider. This closes a real interface restriction; it does not
construct the upstream probes or accept the original unconditional target.
-/

noncomputable section
open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A complete actual paired-probes output on an atlas that the upstream
construction may choose for this current map and this finite wave list.
The only additional selected-normal estimate is its zeroth-order gap. -/
def AtlasFlexibleUpgradeProbeProvider : Prop :=
  ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F),
    (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) → PhaseRegular F hF →
    ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F hF),
      ∃ A : BufferedAtlas M E,
        IsSmoothBufferedAtlas A ∧
        (∀ i, IsCompact (A.support i)) ∧
        (∀ x, ∃ i, x ∈ A.support i) ∧
        ∃ probe : ExactProbeFamily F hF A waves,
          Nonempty (ChosenProbeNormalGap probe)

/-- Every invocation uses the actual same-family atlas construction. No
additional provider on the requested atlas is assumed. -/
theorem AtlasFlexibleUpgradeProbeProvider.on_fixedAtlas [T2Space M]
    (provider : AtlasFlexibleUpgradeProbeProvider (n := n) (N := N) (M := M))
    (B : BufferedAtlas M E) (hB : IsSmoothBufferedAtlas B)
    (hBc : ∀ i, IsCompact (B.support i)) :
    GapControlledUpgradeProbeProvider (N := N) B := by
  intro F hF himm hphase r waves
  obtain ⟨A, hA, hAc, hcoverA, probe, hgap⟩ := provider F hF himm hphase r waves
  obtain ⟨probeB, _, _, _, hgapB⟩ :=
    probe.exists_changeAtlas_with_gap hgap B hA hB hAc hBc hcoverA
  exact ⟨probeB, hgapB⟩

/-- Conditional upgrade in the literal original C² norm, allowing the full
probes construction to choose its atlas separately at each current map/list.
Actual rank, bad-set removal, protection and compact assembly are conclusions
of the compiled geometry chain, never fields of this provider. -/
theorem exists_originalAtlas_sameMetric_phase_embedding_of_atlas_flexible_probes
    [T2Space M] [CompactSpace M]
    (provider : AtlasFlexibleUpgradeProbeProvider (n := n) (N := N) (M := M))
    (A₀ : BufferedAtlas M E) (hA₀ : IsSmoothBufferedAtlas A₀)
    (hA₀c : ∀ i, IsCompact (A₀.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A₀ 2 (G - F) ≠ ⊤ ∧
      (probeAtlasCj A₀ 2 (G - F)).toReal < epsilon := by
  obtain ⟨B, hB, hBc, _, hcoverB, _⟩ :=
    exists_compact_smooth_bufferedAtlas (M := M) («E» := E)
  exact exists_originalAtlas_sameMetric_phase_embedding_of_fixed_gap_probes
    B hB hBc hcoverB (provider.on_fixedAtlas B hB hBc)
      A₀ hA₀ hA₀c F hF himm hphase hn hN hepsilon

#print axioms AtlasFlexibleUpgradeProbeProvider.on_fixedAtlas
#print axioms exists_originalAtlas_sameMetric_phase_embedding_of_atlas_flexible_probes

end GlobalEmbedding.Upgrade
