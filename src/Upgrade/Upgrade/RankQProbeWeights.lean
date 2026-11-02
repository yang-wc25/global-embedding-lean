import Upgrade.CompactLegalWaves

/-!
# Returned probe weights for a preselected duplicated rank-q packet

The global finite list is already fixed. Its injective labels retain two
separate parameter labels for each identical local wave. The provider's
actual overlap-distinctness field, applied at the common cutoff-one center,
gives the unequal weight pair required by the accepted duplicated algebra.
No waves are chosen after the provider returns its weights.
-/

noncomputable section
open Manifold Module Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Both copies belong to the actual common support, so the exact provider
contract supplies positive and unequal weights for the fixed packet. -/
theorem RankQLocalWavePacket.returned_weights
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y)
    (A : BufferedAtlas M E) {r : ℕ} (waves : Fin r → LocalLegalWave F hF)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Function.Injective labels)
    (hlabels : ∀ ij, waves (labels ij) = p.waves ij.1)
    (probe : ExactProbeFamily F hF A waves) :
    (∀ i j, 0 < probe.weight (labels (i,j))) ∧
      (∀ i, probe.weight (labels (i,0)) ≠ probe.weight (labels (i,1))) := by
  have hone (i : Fin n) (j : Fin 2) : (waves (labels (i,j))).cutoff x = 1 := by
    rw [hlabels]
    exact p.one_near.self_of_nhds i
  have hs (i : Fin n) (j : Fin 2) : x ∈ tsupport ((waves (labels (i,j))).cutoff : M → ℝ) :=
    subset_tsupport _ (by
      change (waves (labels (i,j))).cutoff x ≠ 0
      rw [hone]
      exact one_ne_zero)
  refine ⟨fun i j ↦ probe.weight_pos _, ?_⟩
  intro i
  apply probe.distinct_on_overlap
  · intro h
    have he : (0 : Fin 2) = 1 := congrArg Prod.snd (hinj h)
    exact (by decide : (0 : Fin 2) ≠ 1) he
  · exact ⟨x, hs i 0, hs i 1⟩

end GlobalEmbedding.Upgrade
