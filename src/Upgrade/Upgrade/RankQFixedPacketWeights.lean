import Upgrade.CompactLegalWaves
import Upgrade.RankQActualLegalSpace
import Upgrade.RankQFixedPacketAlgebra
import Upgrade.RankQLegalSchurDerivative

/-!
# One actual wave packet for every later returned unequal weight pair

The packet is chosen by `exists_rankQ_localLegalWave_packet` before probes.
All columns below are its literal global tensors/values at the same reference
point. Positivity and unequal weights enter only after that choice. No actual
incidence-rank premise or newly selected packet is used.
-/

noncomputable section
open Manifold Module Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The already accepted onto response is literally the sum of the actual
normal blocks of the SAME fixed global wave tensors. -/
theorem rankQWaveNormalBlock_eq_sum
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (x : M) (waves : Fin n → LocalLegalWave F hF) (t : Fin n → ℝ) :
    rankQWaveNormalBlock F hF x waves t =
      ∑ i, t i • rankQNormalBlock (rankQActualReference F hF x)
        ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((waves i).tensor x)) := by
  exact rankQNormalBlock_sum_comp (S := SymmetricSquare E)
    (W := normalSpace (I := IM) F x)
    (rankQActualReference F hF x) (normalSpace (I := IM) F x).orthogonalProjectionOnto
    (fun i ↦ (waves i).tensor x) t

end GlobalEmbedding.Upgrade
