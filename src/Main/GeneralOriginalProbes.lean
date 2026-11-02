import Main.GeneralOriginalNativeProbes
import Main.GeneralProbeAtlasTransport
import Main.GeneralEndpointStatements

/-!
# Full paired probes from the original qualitative immersion

The actual arbitrary-cutoff family is manufactured internally, then its
unchanged maps and orthogonal normal identifications are transported to the
requested original atlas. The target statements are imported from a separate
statement-only module. No final probe, source supplier, quantitative reference
geometry or repair theorem is a premise of these endpoints.

`original_paired_probes` retains the paper's coordinate-supported input class.
The stronger open-support and local-presentation statements are also exposed.
All three retain every parameter, norm and response field of the same actual
family, including empty sources and empty finite lists.
-/

noncomputable section
open Set Manifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Main
open GlobalEmbedding.Continuation GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

universe uM

/-- The manufactured unrestricted native provider in the original dimension
notation. The chosen complete data is internal to the proof. -/
theorem general_native_probe_provider
    {n N : ℕ} {M : Type uM}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (hn : 2 ≤ n) (hN : n*(n+1)/2 < N) :
    GeneralNativeProbeProvider (n := n) (N := N) (M := M) := by
  cases n with
  | zero => omega
  | succ m =>
    apply generalNativeProbeProvider_from_original
    · simpa only [Nat.succ_eq_add_one] using hn
    · simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hN

/-- The full arbitrary smooth-cutoff theorem on every requested compact
smooth covering atlas. Its estimates and geometric data are all outputs. -/
theorem general_paired_probes : GeneralProbesTarget.{uM} := by
  intro n N M _ _ _ _ _ _ hn hN F hF hi hphase A hA hcompact hcover r waves
  obtain ⟨B,hB,hBc,hBcover,⟨native⟩⟩ :=
    general_native_probe_provider hn hN F hF hi hphase r waves
  exact ⟨native.toGeneralExactProbeFamily.changeAtlas A hB hA hBc hcompact hBcover⟩

/-- The paper's exact coordinate-supported paired second-form and value
probes, with all four estimates and the bounded spatial C³ assertion. -/
theorem original_paired_probes : PaperProbesTarget.{uM} :=
  general_paired_probes.toPaper

/-- The same construction for locally presented cutoff, phase and normal
data, using the proved smooth zero extension and the same local germs. -/
theorem locally_presented_paired_probes : LocallyPresentedProbesTarget.{uM} :=
  general_paired_probes.toLocallyPresented

end GlobalEmbedding.Main

#print axioms GlobalEmbedding.Main.general_native_probe_provider
#print axioms GlobalEmbedding.Main.general_paired_probes
#print axioms GlobalEmbedding.Main.original_paired_probes
#print axioms GlobalEmbedding.Main.locally_presented_paired_probes
