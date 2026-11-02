import Upgrade.SupportedProbePackets
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Supported source packets without a supplied second point

The n≥4 supported-kernel operation acts on source points rather than pairs.
The existing local legal-wave theorem allows a distinct partner to be kept
outside its support. Positive source dimension supplies such a partner inside
the actual source chart, so this internal construction adds no extra point or
connectedness hypothesis to the source operation. Empty sources are automatic.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

omit [IsManifold IM ∞ M] [BoundarylessManifold IM M] in
/-- A positive-dimensional native manifold has another point in every actual
chart centered at a given point. No global nonempty or connectedness input is
used: the statement is vacuous if the manifold is empty. -/
theorem exists_distinct_point_in_actual_chart
    (hn : 0 < n) (x : M) : ∃ y ∈ (chartAt E x).source, x ≠ y := by
  let : NeZero n := ⟨hn.ne'⟩
  let : PerfectSpace E := perfectSpace_of_module ℝ E
  let c : E := chartAt E x x
  have hc : c ∈ (chartAt E x).target := (chartAt E x).map_source (mem_chart_source E x)
  have htarget : (chartAt E x).target ∈ 𝓝[≠] c :=
    mem_nhdsWithin_of_mem_nhds ((chartAt E x).open_target.mem_nhds hc)
  have hne : {c}ᶜ ∈ 𝓝[≠] c := self_mem_nhdsWithin
  obtain ⟨z, hzt, hzc⟩ := Filter.nonempty_of_mem (inter_mem htarget hne)
  refine ⟨(chartAt E x).symm z, (chartAt E x).map_target hzt, ?_⟩
  intro hxy
  apply hzc
  change z = c
  calc
    z = chartAt E x ((chartAt E x).symm z) := ((chartAt E x).right_inv hzt).symm
    _ = c := congrArg (chartAt E x) hxy.symm

/-- The source supported-kernel operation gets its actual q wave packet
without requesting a second point. The selected partner and all waves are
constructed from the actual source chart and the accepted strong rank theorem. -/
theorem exists_supported_source_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x : M) (honto : Function.Surjective (trueSecondForm F hF x))
    (hsupported : HasSupportedKernel (trueSecondForm F hF x)) :
    ∃ y : M, x ≠ y ∧ Nonempty (SupportedLocalWavePacket F hF x y) := by
  obtain ⟨y, _, hxy⟩ := exists_distinct_point_in_actual_chart (by omega : 0 < n) x
  exact ⟨y, hxy, exists_supported_localLegalWave_packet F hF himm hphase hn hN x y hxy honto hsupported⟩

#print axioms exists_distinct_point_in_actual_chart
#print axioms exists_supported_source_localLegalWave_packet

end GlobalEmbedding.Upgrade
