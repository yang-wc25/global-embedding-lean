import NormalPolar.NativeProbeConstruction
import Round2.AtlasFlexibleProbeIntegration

/-!
# The original upgrade consumer from native actual-map probe data

The upstream obligation now concerns actual smooth maps, their exact metric
and native jet budgets. The supplied data contains no Q, Q regularity, Q
response, same-Q gap or identified second-form response. Those are constructed
before calling the existing geometric upgrade. This does not assert that the
remaining native analytic family exists and does not accept an original target.
-/

noncomputable section
open Set Filter Manifold Topology GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- A provider of actual native analytic data may choose its fixed compact
atlas after the current immersion and actual finite wave list. For each such
invocation its map, weights, radius and threshold are used unchanged. -/
def NativeUpgradeProbeProvider : Prop :=
  ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)),
    PhaseRegular F hF → ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F hF),
      ∃ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
        (hcompact : ∀ i, IsCompact (A.support i))
        (hcover : ∀ x, ∃ i, x ∈ A.support i),
        Nonempty (NativeProbeData F hF A hA hcompact hcover hi waves)

/-- Native actual data supplies the full original probe and its same-Q gap;
no normal-bundle conclusion is added to the upstream provider. -/
theorem NativeUpgradeProbeProvider.toAtlasFlexible [T2Space M]
    (provider : NativeUpgradeProbeProvider (n := n) (N := N) (M := M)) :
    AtlasFlexibleUpgradeProbeProvider (n := n) (N := N) (M := M) := by
  intro F hF hi hphase r waves
  obtain ⟨A, hA, hcompact, hcover, ⟨d⟩⟩ := provider F hF hi hphase r waves
  exact ⟨A, hA, hcompact, hcover, d.toExactProbeFamily, ⟨d.chosenNormalGap⟩⟩

/-- The existing same-family atlas transport moves the constructed full probe
to the fixed native atlas used by the geometric consumer. -/
theorem NativeUpgradeProbeProvider.on_fixedAtlas [T2Space M]
    (provider : NativeUpgradeProbeProvider (n := n) (N := N) (M := M))
    (B : BufferedAtlas M E) (hB : IsSmoothBufferedAtlas B)
    (hcompact : ∀ i, IsCompact (B.support i)) :
    GapControlledUpgradeProbeProvider (N := N) B :=
  provider.toAtlasFlexible.on_fixedAtlas B hB hcompact

/-- The existing original-norm geometric upgrade now consumes native actual
mapping families and jet estimates. Existence of those analytic families is
the explicit remaining upstream obligation. -/
theorem exists_originalAtlas_sameMetric_phase_embedding_of_native_probes
    [T2Space M] [CompactSpace M]
    (provider : NativeUpgradeProbeProvider (n := n) (N := N) (M := M))
    (A₀ : BufferedAtlas M E) (hA₀ : IsSmoothBufferedAtlas A₀)
    (hA₀c : ∀ i, IsCompact (A₀.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A₀ 2 (G - F) ≠ ⊤ ∧
      (probeAtlasCj A₀ 2 (G - F)).toReal < epsilon :=
  exists_originalAtlas_sameMetric_phase_embedding_of_atlas_flexible_probes
    provider.toAtlasFlexible A₀ hA₀ hA₀c F hF hi hphase hn hN hepsilon

end GlobalEmbedding.NormalPolar
