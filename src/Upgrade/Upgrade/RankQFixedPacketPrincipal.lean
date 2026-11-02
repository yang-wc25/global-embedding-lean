import Upgrade.RankQFixedPacketProjection
import Upgrade.RankQActualPrincipalRank
import Upgrade.RankQProbeWeights
import Upgrade.RankQFixedWeightSimulation

/-!
# The fixed actual packet and returned weights give principal rank 2n+1

These endpoints use only the original immersion, phase regularity and actual
rank-q stratum, plus the fixed packet constructed from the accepted local
waves. The joint principal map is the literal Schur derivative of its tensors,
its negative inverse-square-weighted global values, and the actual original
first-source differential. Its rank is proved, never supplied as a premise.
-/

noncomputable section
open Manifold Module
open scoped ContDiff Topology
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


/-- The same literal actual principal map for this fixed packet. -/
def RankQLocalWavePacket.principalMap
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y) (lambda : Fin n → Fin 2 → ℝ) :=
  rankQActualJointPrincipalMap (I := IM) F hF x
    (fun ij : Fin n × Fin 2 ↦ (p.waves ij.1).tensor x)
    (fun ij : Fin n × Fin 2 ↦ -((lambda ij.1 ij.2 ^ 2)⁻¹) • (p.waves ij.1).value x)

/-- The actual projected span required by the old geometric rank consumer is
computed from the fixed packet and arbitrary later unequal returned weights. -/
theorem RankQLocalWavePacket.projected_principal_dimension
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular (I := IM) F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm (I := IM) F hF x).range = n * (n - 1) / 2)
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    finrank ℝ (Submodule.span ℝ (Set.range
      (fun ij : Fin n × Fin 2 ↦ rankQActualJointProjection (I := IM) F hF x
        (rankQActualPrincipalColumn (I := IM) F hF x ((p.waves ij.1).tensor x)
          (-((lambda ij.1 ij.2 ^ 2)⁻¹) • (p.waves ij.1).value x))))) = n + 1 := by
  have hp := p.duplicated_projected_finrank himm hphase hn hN hrank lambda hlambda hne
  exact hp

/-- Full principal joint rank, with the original source differential. -/
theorem RankQLocalWavePacket.principalMap_rank
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular (I := IM) F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm (I := IM) F hF x).range = n * (n - 1) / 2)
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    2 * n + 1 ≤ finrank ℝ (p.principalMap lambda).range := by
  exact rankQActualJointPrincipalMap_finrank (I := IM) F hF x himm _ _
    (p.projected_principal_dimension himm hphase hn hN hrank lambda hlambda hne)

/-- Actual preimages of one independent frame of the same principal map. -/
theorem RankQLocalWavePacket.principalMap_finite_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular (I := IM) F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm (I := IM) F hF x).range = n * (n - 1) / 2)
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    ∃ d : Fin (2 * n + 1) → (((Fin n × Fin 2) → ℝ) × E),
      LinearIndependent ℝ (fun j ↦ p.principalMap lambda (d j)) := by
  exact rankQActualJointPrincipalMap_finite_frame (I := IM) F hF x himm _ _
    (p.projected_principal_dimension himm hphase hn hN hrank lambda hlambda hne)

/-- Choose the reference frame with weights 1 and 2 BEFORE the finite cover
and before the provider is called. Returned weights are simulated later by
`simulate_fixed_weights`; this frame and its neighborhoods are not reselected. -/
theorem RankQLocalWavePacket.preparation_principal_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular (I := IM) F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm (I := IM) F hF x).range = n * (n - 1) / 2) :
    ∃ d : Fin (2 * n + 1) → (((Fin n × Fin 2) → ℝ) × E),
      LinearIndependent ℝ (fun j ↦ p.principalMap rankQPreparationWeights (d j)) := by
  exact p.principalMap_finite_frame himm hphase hn hN hrank _
    rankQPreparationWeights_pos rankQPreparationWeights_ne

/-- The provider is called on the already fixed global list. Its returned
weights automatically satisfy the two-copy conditions, and supply this
frame without any further rank or weight hypothesis. -/
theorem RankQLocalWavePacket.returned_probe_principal_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket (n := n) (N := N) F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular (I := IM) F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm (I := IM) F hF x).range = n * (n - 1) / 2)
    (A : BufferedAtlas M E) {r : ℕ} (waves : Fin r → LocalLegalWave F hF)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Function.Injective labels)
    (hlabels : ∀ ij, waves (labels ij) = p.waves ij.1)
    (probe : ExactProbeFamily F hF A waves) :
    ∃ d : Fin (2 * n + 1) → (((Fin n × Fin 2) → ℝ) × E),
      LinearIndependent ℝ (fun j ↦
        p.principalMap (fun i k ↦ probe.weight (labels (i,k))) (d j)) := by
  obtain ⟨hpos, hne⟩ := p.returned_weights A waves labels hinj hlabels probe
  exact p.principalMap_finite_frame himm hphase hn hN hrank _ hpos hne

#check RankQLocalWavePacket.principalMap
#print axioms RankQLocalWavePacket.principalMap_rank
#print axioms RankQLocalWavePacket.preparation_principal_frame
#print axioms RankQLocalWavePacket.returned_probe_principal_frame

end GlobalEmbedding.Upgrade
