import Round2.AtlasProbeTransport
import Round2.CompactGapProbeProvider

/-!
# Same-gap complete-family and provider transport to a geometric atlas

The full quantitative family is actually reconstructed on the requested
atlas by `ExactProbeFamily.changeAtlas`; its map, Q, parameters and weights
are unchanged. This file transports the SAME gap and calls that construction
for every current map and every newly prepared finite wave list. It adds no
new probes field, incidence rank or conclusion of the upgrade theorem.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original gap function for the original identification is retained
by the complete family on the new atlas. -/
def ChosenProbeNormalGap.changeAtlas
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalGap probe)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    ChosenProbeNormalGap (probe.changeAtlas B hA hB hAc hBc hcoverA) :=
  control.transportSameGeometry hcoverA (probe.changeAtlas B hA hB hAc hBc hcoverA) rfl

@[simp] theorem ChosenProbeNormalGap.changeAtlas_gap
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalGap probe)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (control.changeAtlas B hA hB hAc hBc hcoverA).gap = control.gap := rfl

/-- A direct existential interface: the new complete family has the SAME
geometry and weights, and has an actual chosen gap whenever the old one does. -/
theorem ExactProbeFamily.exists_changeAtlas_with_gap
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (hgap : Nonempty (ChosenProbeNormalGap probe))
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    ∃ probeB : ExactProbeFamily F₀ hF₀ B waves,
      probeB.toProbeGeometry = probe.toProbeGeometry ∧
      probeB.weight = probe.weight ∧ probeB.etaV = probe.etaV ∧
      Nonempty (ChosenProbeNormalGap probeB) := by
  obtain ⟨control⟩ := hgap
  exact ⟨probe.changeAtlas B hA hB hAc hBc hcoverA, rfl, rfl, rfl,
    ⟨control.changeAtlas B hA hB hAc hBc hcoverA⟩⟩

/-- One complete same-gap provider on a covering compact smooth atlas gives
the same full provider on any requested compact smooth atlas. Each invocation
uses its current real map and its current actual finite wave list. -/
theorem GapControlledUpgradeProbeProvider.changeAtlas
    {A : BufferedAtlas M E} (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    GapControlledUpgradeProbeProvider (N := N) B := by
  intro F hF himm hphase r waves
  obtain ⟨probe, hgap⟩ := provider F hF himm hphase r waves
  obtain ⟨probeB, _, _, _, hgapB⟩ :=
    probe.exists_changeAtlas_with_gap hgap B hA hB hAc hBc hcoverA
  exact ⟨probeB, hgapB⟩

#print axioms ExactProbeFamily.exists_changeAtlas_with_gap
#print axioms GapControlledUpgradeProbeProvider.changeAtlas

end GlobalEmbedding.Upgrade
