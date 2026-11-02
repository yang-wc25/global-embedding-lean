import Upgrade.CompactSupportedPreparation
import Upgrade.CompactLegalWaves
import Upgrade.ProtectionSupported

/-!
# One finite actual wave list for the current supported source locus

The compact set is recomputed from the current map's literal true second form.
The normal equation tolerance and source neighborhood precede finite selection
and the provider call. The two copies retain distinct labels and exactly the
same legal waves. This construction alone does not assert kernel elimination
in dimension three; its source-avoidance consumer requires n≥4.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_finite_supported_prepared_actualWave_list [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x)) :
    let K := {x ∈ C | HasSupportedKernel (trueSecondForm F hF x)}
    ∃ partners : K → M,
      ∃ packets : ∀ c : K, SupportedLocalWavePacket F hF c.1 (partners c),
      ∃ index : K → Fin A.count,
      ∃ inSupport : ∀ c, c.1 ∈ interior (A.support (index c)),
      ∃ preparation : ∀ c, SupportedPreparedNeighborhood A hA (packets c) (index c) (inSupport c),
      ∃ centers : Finset K, ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
        ∃ labels : (centers × (Fin (n * (n - 1) / 2) × Fin 2)) ≃ Fin r,
          (∀ c : centers, ∀ i j, waves (labels (c, i, j)) = (packets c.1).waves i) ∧
          (∀ z ∈ K, ∃ c ∈ centers, z ∈ (preparation c).neighborhood) ∧
          (∀ c : centers, ∀ i,
            labels (c, i, 0) ≠ labels (c, i, 1) ∧
            (tsupport ((waves (labels (c, i, 0))).cutoff : M → ℝ) ∩
              tsupport ((waves (labels (c, i, 1))).cutoff : M → ℝ)).Nonempty) := by
  classical
  let K := {x ∈ C | HasSupportedKernel (trueSecondForm F hF x)}
  have hK : IsCompact K := isCompact_actual_supported_on_compact_fullRank F hF himm hphase hC hfull
  have hlocal (c : K) := exists_supported_source_localLegalWave_packet F hF himm hphase hn hN
    c.1 (hfull c.1 c.2.1) c.2.2
  choose partners hpartners hasPacket using hlocal
  let packets : ∀ c : K, SupportedLocalWavePacket F hF c.1 (partners c) :=
    fun c ↦ Classical.choice (hasPacket c)
  choose index inSupport using fun c : K ↦ hcoverA c.1
  let preparation : ∀ c : K, SupportedPreparedNeighborhood A hA (packets c) (index c) (inSupport c) :=
    fun c ↦ Classical.choice ((packets c).exists_prepared_neighborhood A hA himm
      (index c) (inSupport c))
  obtain ⟨centers, r, waves, labels, hlabels, hcover⟩ :=
    finite_actual_localLegalWave_list hK
      (fun c (ij : Fin (n * (n - 1) / 2) × Fin 2) ↦ (packets c).waves ij.1)
      (fun c ↦ (preparation c).neighborhood)
      (fun c ↦ (preparation c).neighborhood_open) (fun c ↦ (preparation c).center_mem)
  refine ⟨partners, packets, index, inSupport, preparation, centers, r, waves, labels,
    fun c i j ↦ hlabels c (i, j), hcover, ?_⟩
  intro c i
  constructor
  · apply labels.injective.ne
    intro h
    have h01 : (0 : Fin 2) = 1 := congrArg
      (fun k : centers × (Fin (n * (n - 1) / 2) × Fin 2) ↦ k.2.2) h
    norm_num at h01
  · rw [hlabels c (i, 0), hlabels c (i, 1)]
    have hone : ((packets c.1).waves i).cutoff c.1.1 = 1 :=
      ((packets c.1).one_near.self_of_nhds) i
    have hmem : c.1.1 ∈ tsupport (((packets c.1).waves i).cutoff : M → ℝ) :=
      subset_tsupport _ (by
        change ((packets c.1).waves i).cutoff c.1.1 ≠ 0
        rw [hone]
        norm_num)
    exact ⟨c.1.1, hmem, hmem⟩

end GlobalEmbedding.Upgrade
