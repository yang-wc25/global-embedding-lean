import Probes.Round4ParameterBlocksBeforeMetric
import Probes.Round4ParameterProbeTailCaps

/-!
# Fixed repair choices that can start at the actual first probe map

This is an output record. The producers in this continuation construct its
stage costs and raw increments from the reference geometry. Its restart
field preserves the supplied physical initial map and the same least-wait
trajectory; it is not an assumed ideal step or a final probe estimate.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [CompactSpace M]
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}

/-- One set of numerical choices, fixed before the original probe scale.
Every restart uses exactly the initial map that it is given. All future
states and actual increments are produced by the restart conclusion. -/
structure ActualProbeProducedRepairPlan
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (Β Sub : Type*) [Fintype Β] [Fintype Sub] where
  budget : ℝ
  epsilon : ℝ
  eta : ℝ
  budget_pos : 0 < budget
  epsilon_pos : 0 < epsilon
  eta_pos : 0 < eta
  reference_budget : 4*round3RepairReferenceLowBase packet < budget
  cost : ℕ → Round3RepairPrimitiveCosts
  Cs : ℕ → ℕ → ℝ
  sigma : ℕ → ℝ
  sigma_pos : ∀ k, 0 < sigma k
  small : ∀ k, sigma k ≤ (1/2 : ℝ)^5
  displacement : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1))
  threshold : ∀ k, sigma k < (cost k).Theta^10
  tail_cap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k
  restart : ∀ (t : ℝ) (ht : 0 < t) (ht1 : t < 1), t ≤ sigma 0 →
    ∀ initial : Round3RepairClosedState packet budget epsilon eta 10 t,
    Nonempty (Round3RepairInfiniteBlocks (Tr := ℝ) (Λ := Fin Data.primaryCount)
      (Β := Β) (SubSecondary := Sub) packet cost Cs sigma budget epsilon eta t ht ht1 initial)

end GlobalEmbedding.Continuation

