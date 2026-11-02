import Upgrade.CompactSupportedJointPreparation
import Upgrade.CompactLegalWaves
import Upgrade.ProtectionSupported

/-!
# Actual finite preparation of supported coincidences, including n=3

The current joint bad set is compact on a compact full-rank pair region.
Its actual common support/value packet and fixed-weight geometric neighborhood
are selected before the single finite probes list. Nothing here says that all
supported kernels can be removed in dimension three.
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

theorem isCompact_actual_supportedCoincidence_on_compact_fullRank [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) {P : Set (M × M)} (hP : IsCompact P)
    (hfull : ∀ z ∈ P, Function.Surjective (trueSecondForm F hF z.1)) :
    IsCompact {z ∈ P | HasSupportedKernel (trueSecondForm F hF z.1) ∧ F z.1 = F z.2} := by
  have hgood := (isOpen_actual_fullRank_nonsupported F hF himm hphase).preimage
    (show Continuous (Prod.fst : M × M → M) from continuous_fst)
  have hc := (hP.diff hgood).inter_right
    (isClosed_eq (hF.continuous.comp continuous_fst) (hF.continuous.comp continuous_snd))
  convert hc using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, Set.mem_sdiff, mem_preimage]
  constructor
  · rintro ⟨hz, hs, heq⟩
    exact ⟨⟨hz, fun h ↦ h.2 hs⟩, heq⟩
  · rintro ⟨⟨hz, hs⟩, heq⟩
    exact ⟨hz, by_contra (fun h ↦ hs ⟨hfull z hz, h⟩), heq⟩

theorem exists_finite_supportedJoint_prepared_actualWave_list [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P) (hdistinct : ∀ z ∈ P, z.1 ≠ z.2)
    (hfull : ∀ z ∈ P, Function.Surjective (trueSecondForm F hF z.1)) :
    let K := {z ∈ P | HasSupportedKernel (trueSecondForm F hF z.1) ∧ F z.1 = F z.2}
    ∃ packets : ∀ c : K, SupportedJointWavePacket F hF c.1.1 c.1.2,
      ∃ index : K → Fin A.count,
      ∃ inSupport : ∀ c, c.1.1 ∈ interior (A.support (index c)),
      ∃ preparation : ∀ c, SupportedJointPreparedNeighborhood A hA (packets c) (index c) (inSupport c),
      ∃ centers : Finset K, ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
        ∃ labels : (centers × (Fin (n * (n - 1) / 2 + n) × Fin 2)) ≃ Fin r,
          (∀ c : centers, ∀ i j, waves (labels (c, i, j)) = (packets c.1).waves i) ∧
          (∀ z ∈ K, ∃ c ∈ centers, z ∈ (preparation c).neighborhood) ∧
          (∀ c : centers, ∀ i,
            labels (c, i, 0) ≠ labels (c, i, 1) ∧
            (tsupport ((waves (labels (c, i, 0))).cutoff : M → ℝ) ∩
              tsupport ((waves (labels (c, i, 1))).cutoff : M → ℝ)).Nonempty) := by
  classical
  let K := {z ∈ P | HasSupportedKernel (trueSecondForm F hF z.1) ∧ F z.1 = F z.2}
  have hK : IsCompact K := isCompact_actual_supportedCoincidence_on_compact_fullRank F hF himm hphase hP hfull
  let packets : ∀ c : K, SupportedJointWavePacket F hF c.1.1 c.1.2 := fun c ↦
    Classical.choice (exists_supported_joint_localLegalWave_packet F hF himm hphase hn hN
      c.1.1 c.1.2 (hdistinct c.1 c.2.1) (hfull c.1 c.2.1) c.2.2.1)
  choose index inSupport using fun c : K ↦ hcoverA c.1.1
  let preparation : ∀ c : K, SupportedJointPreparedNeighborhood A hA (packets c) (index c) (inSupport c) :=
    fun c ↦ Classical.choice ((packets c).exists_prepared_neighborhood A hA himm
      (index c) (inSupport c))
  obtain ⟨centers, r, waves, labels, hlabels, hcover⟩ :=
    finite_actual_localLegalWave_list hK
      (fun c (ij : Fin (n * (n - 1) / 2 + n) × Fin 2) ↦ (packets c).waves ij.1)
      (fun c ↦ (preparation c).neighborhood)
      (fun c ↦ (preparation c).neighborhood_open) (fun c ↦ (preparation c).center_mem)
  refine ⟨packets, index, inSupport, preparation, centers, r, waves, labels,
    fun c i j ↦ hlabels c (i, j), hcover, ?_⟩
  intro c i
  constructor
  · apply labels.injective.ne
    intro h
    have h01 : (0 : Fin 2) = 1 := congrArg
      (fun k : centers × (Fin (n * (n - 1) / 2 + n) × Fin 2) ↦ k.2.2) h
    norm_num at h01
  · rw [hlabels c (i, 0), hlabels c (i, 1)]
    have hone : ((packets c.1).waves i).cutoff c.1.1.1 = 1 :=
      ((packets c.1).one_near.self_of_nhds) i
    have hmem : c.1.1.1 ∈ tsupport (((packets c.1).waves i).cutoff : M → ℝ) :=
      subset_tsupport _ (by
        change ((packets c.1).waves i).cutoff c.1.1.1 ≠ 0
        rw [hone]
        norm_num)
    exact ⟨c.1.1.1, hmem, hmem⟩

end GlobalEmbedding.Upgrade
