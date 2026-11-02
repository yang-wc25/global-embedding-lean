import Main.GeneralOriginalProbes
import Main.SmallImmersionUpgrade

/-!
# Original upgrade and main from the manufactured native probes

These endpoints supply the formerly explicit native analytic provider from
the complete arbitrary-cutoff paired-probe construction on the actual original
immersion. The specialization retains the same map and actual normal geometry. The existing normal-identification and
geometric-upgrade chain, and the accepted small-immersion theorem, are reused.
The general native uniform repair statement is not an input.

The embedding conclusion is stated through the actual smooth map, injective
native differential, and topological embedding. No unproved conversion to
Mathlib's chart-normal-form IsSmoothEmbedding is used.
-/

noncomputable section
open Set Manifold Bundle Topology
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Main
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

universe uM
variable {n N : ℕ} {M : Type uM}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- The actual native provider in the original dimension notation. -/
theorem native_probe_provider (hn : 2 ≤ n) (hN : n*(n+1)/2 < N) :
    NativeUpgradeProbeProvider (n := n) (N := N) (M := M) := by
  exact (general_native_probe_provider hn hN).toNativeUpgradeProbeProvider

/-- The original same-metric embedding upgrade, with its original C²
approximation norm and no native-probes supply hypothesis. -/
theorem original_sameMetric_phase_embedding
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hAc : ∀ i, IsCompact (A.support i))
    (hAcover : ∀ x, ∃ i, x ∈ A.support i)
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (hPhase : PhaseRegular F0 hF0)
    (hn : 3 ≤ n) (hN : N = n*(n+1)/2+1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ,V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F0 x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A 2 (G-F0) ≠ ⊤ ∧ (probeAtlasCj A 2 (G-F0)).toReal < epsilon := by
  exact exists_originalAtlas_sameMetric_phase_embedding_of_native_probes
    (native_probe_provider (by omega) (by omega)) A hA hAc F0 hF0 hImm hPhase hn hN hepsilon

/-- The full closed parallelizable main statement, including arbitrary
positive image radius and the same map's prescribed metric and embedding. -/
theorem endpoint_main : EndpointMainTarget.{uM} := by
  apply endpoint_main_of_native_probes
  intro k X _ _ _ _ _ _ hk
  exact native_probe_provider (by omega) (by omega)

end GlobalEmbedding.Main

#print axioms GlobalEmbedding.Main.native_probe_provider
#print axioms GlobalEmbedding.Main.original_sameMetric_phase_embedding
#print axioms GlobalEmbedding.Main.endpoint_main
