import Upgrade.CompactLegalWaves
import Upgrade.CompactTrueRank
import GlobalEmbedding.Paper.SymmetricSquareFinrank

/-!
# The actual old rank-q coincidence set and its fixed finite wave list

Original phase regularity itself excludes lower ranks.  Thus the rank-q
coincidence set is the closed low-rank incidence already treated above.  Its
finite actual packets are chosen before probe weights, with two distinct
labels for each repeated legal wave.  The chosen neighborhoods here retain
the actual cutoff geometry; further Schur derivative margins are separate.
-/

noncomputable section
open Bundle Filter Manifold Module Set GlobalEmbedding.Paper
open scoped Topology ContDiff BigOperators

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The elementary rank bound needed for compactness follows directly from
the actual good covector's injective Sym² restriction and the accepted Sym²
dimension formula.  No supported-kernel classification is repeated. -/
theorem phaseRegular_trueSecondForm_rank_lower
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hphase : PhaseRegular F hF) (x : M) :
    n * (n - 1) / 2 ≤ finrank ℝ (trueSecondForm F hF x).range := by
  obtain ⟨xi, hxi⟩ := hphase x
  have hxilm : xi.toLinearMap ≠ 0 := by
    intro hz
    apply hxi.1
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hz v
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hxilm
  have hdim : finrank ℝ (TangentSpace IM x) = n := finrank_euclideanSpace_fin
  rw [hdim] at hker
  have hkd : finrank ℝ xi.ker = n - 1 := by omega
  have hn : 1 ≤ n := by omega
  have hrange := LinearMap.finrank_range_of_inj hxi.2
  have hmono := Submodule.finrank_mono
    (LinearMap.range_comp_le_range (symmetricSquareLinearMap xi.ker.subtype)
      (trueSecondForm F hF x))
  rw [hrange, symmetricSquare_finrank, hkd, Nat.sub_add_cancel hn] at hmono
  simpa only [Nat.mul_comm] using hmono

/-- The actual rank-q coincidence set, retaining the whole compact pair set.
The latter may contain pairs on different connected components. -/
def rankQCoincidenceSet
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (P : Set (M × M)) : Set (M × M) :=
  {z ∈ P | finrank ℝ (trueSecondForm F hF z.1).range = n * (n - 1) / 2 ∧
    F z.1 = F z.2}

theorem isCompact_rankQCoincidenceSet
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) {P : Set (M × M)} (hP : IsCompact P) :
    IsCompact (rankQCoincidenceSet F hF P) := by
  have hlow := isCompact_trueSecondForm_lowRank_coincidence F hF himm
    (n * (n - 1) / 2) hP
  convert hlow using 1
  ext z
  change (z ∈ P ∧ finrank ℝ (trueSecondForm F hF z.1).range = n * (n - 1) / 2 ∧
      F z.1 = F z.2) ↔
    (z ∈ P ∧ finrank ℝ (trueSecondForm F hF z.1).range ≤ n * (n - 1) / 2 ∧
      F z.1 = F z.2)
  constructor
  · exact fun hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩
  · intro hz
    exact ⟨hz.1, le_antisymm hz.2.1
      (phaseRegular_trueSecondForm_rank_lower F hF hphase z.1), hz.2.2⟩

/-- One finite doubled list of actual legal waves for the old actual rank-q
coincidence set.  Selected local packets remain available with their onto
normal-block derivative.  The actual shared cutoff supports meet, so the
probe provider's distinct-on-overlap rule applies to the two labels later.
No weights or perturbed map have been chosen at this point. -/
theorem exists_finite_rankQ_actualWave_list [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    {P : Set (M × M)} (hP : IsCompact P)
    (hdistinct : ∀ z ∈ P, z.1 ≠ z.2) :
    let K := rankQCoincidenceSet F hF P
    ∃ packets : ∀ c : K, RankQLocalWavePacket F hF c.1.1 c.1.2,
      ∃ O : K → Set (M × M),
        (∀ c, IsOpen (O c) ∧ c.1 ∈ O c ∧
          ∀ z ∈ O c, ∀ i,
            ((packets c).waves i).cutoff z.1 = 1 ∧
              ((packets c).waves i).cutoff z.2 = 0) ∧
        ∃ centers : Finset K, ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
          ∃ labels : (centers × (Fin n × Fin 2)) ≃ Fin r,
            (∀ c : centers, ∀ i j,
              waves (labels (c, i, j)) = (packets c.1).waves i) ∧
            (∀ z ∈ K, ∃ c ∈ centers, z ∈ O c) ∧
            (∀ c : centers, ∀ i,
              labels (c, i, 0) ≠ labels (c, i, 1) ∧
              (tsupport ((waves (labels (c, i, 0))).cutoff : M → ℝ) ∩
                tsupport ((waves (labels (c, i, 1))).cutoff : M → ℝ)).Nonempty) := by
  classical
  let K := rankQCoincidenceSet F hF P
  have hK : IsCompact K := isCompact_rankQCoincidenceSet F hF himm hphase hP
  have hp (c : K) : Nonempty (RankQLocalWavePacket F hF c.1.1 c.1.2) :=
    exists_rankQ_localLegalWave_packet F hF himm hphase hn hN c.1.1 c.1.2
      (hdistinct c.1 c.2.1) c.2.2.1
  let packets : ∀ c : K, RankQLocalWavePacket F hF c.1.1 c.1.2 :=
    fun c ↦ Classical.choice (hp c)
  choose O hO hcO hcutoff using fun c : K ↦ (packets c).exists_pair_neighborhood
  obtain ⟨centers, r, waves, labels, hlabels, hcover⟩ :=
    finite_actual_localLegalWave_list hK
      (fun c (ij : Fin n × Fin 2) ↦ (packets c).waves ij.1) O hO hcO
  refine ⟨packets, O, fun c ↦ ⟨hO c, hcO c, hcutoff c⟩,
    centers, r, waves, labels, ?_, hcover, ?_⟩
  · intro c i j
    exact hlabels c (i, j)
  · intro c i
    constructor
    · apply labels.injective.ne
      intro h
      have h01 : (0 : Fin 2) = 1 := congrArg
        (fun k : centers × (Fin n × Fin 2) ↦ k.2.2) h
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
