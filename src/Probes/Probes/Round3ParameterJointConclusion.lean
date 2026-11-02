import Probes.Round3ParameterWholeDomainRegularity
import Probes.Round3ParameterMetricAddition
import Probes.Round3ParameterActualIncrementNorms
import Probes.Round3ParameterActualMetricRemainder
import Smoothing.Round3ParameterMeanResidualMembership

/-! The desired simultaneous output for one literal global increment.
Every regularity and norm field is a conclusion, never an input to the raw
construction.  The same U, H, physical W and all original chart domains are
used for every observation order. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

structure Round3ParameterJointIncrementConclusion
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (q : ℕ) (delta tau ell : ℝ) (Cmap Cmetric : ℕ → ℝ) : Prop where
  joint_smooth : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U W
  map_germs : ∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
    G ⊆ incrementsOriginalDifferentiation A B i ∧
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) G
  metric_germ : incrementsOriginalMetricError F U H delta ∈ parameterRound2_originalTensorGermSpace A B S W
  map0 : ∀ j, paperAtlasWeighted 0 (j+1) tau (incrementsOriginalMapCoordinates A B U)
    (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 (j+1) tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ Cmap j*delta*tau
  map1 : ∀ j, paperAtlasWeighted 1 j tau (incrementsOriginalMapCoordinates A B U)
    (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 1 j tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ Cmap j*delta
  metric : ∀ j, paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
    (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S).toReal ≤
      Cmetric j*(delta*(tau/ell)^q+delta^3/tau)

end GlobalEmbedding.Continuation
