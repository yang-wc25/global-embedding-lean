import Probes.Round3ParameterRawAtlasData
import Smoothing.ParameterRound2MeanPrimitives

/-! Original tensor coordinates of the same general-parameter mean error.
The exact native mean identity is consumed only after the actual global
family has been pulled back through the genuine parameter chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_original_meanError_coordinates
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (P × M)) (primary : Λ → Set (P × M))
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau)
    (i : Fin A.count × Fin c)
    (h : ParameterRound2GlobalMeanPrimitives
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) (fun t => input ((B i.2).symm t))
      (round3ParameterNativeDomain (B i.2) W) (fun ν => round3ParameterNativeDomain (B i.2) (primary ν)))
    (y : Fin (m+1+d) → ℝ) (hy : y ∈ incrementsOriginalDifferentiation A B i)
    (hW : (incrementsOriginalParameterPoint y,(A.chart i.1).symm (incrementsOriginalSourcePoint y)) ∈
      round3ParameterNativeDomain (B i.2) W) :
    incrementsOriginalTensorCoordinates A B (round3ParameterPrimaryMeanError F hF g input (q+2) tau) i y =
    fun k => (parameterRound2_globalObservedMeanCoefficient
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) (fun t => input ((B i.2).symm t))
      (q+2) tau (A.chart i.1) (incrementsOriginalParameterPoint y,incrementsOriginalSourcePoint y)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).re := by
  funext k
  have hm := round3ParameterPrimary_pullback_meanError F hF g (B i.2) hg input (q+2) tau
    (incrementsOriginalParameterPoint y) hy.2 ((A.chart i.1).symm (incrementsOriginalSourcePoint y))
  change round3ParameterPrimaryMeanError F hF g input (q+2) tau
    ((B i.2).symm (incrementsOriginalParameterPoint y))
    ((A.chart i.1).symm (incrementsOriginalSourcePoint y)) _ _ = _
  rw [← hm]
  exact parameterRound2_meanPrimitives_coordinate
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2)) (fun t => input ((B i.2).symm t))
    (round3ParameterNativeDomain (B i.2) W) (fun ν => round3ParameterNativeDomain (B i.2) (primary ν))
    h q hq tau htau (A.chart i.1)
    (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i.1))
    (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i.1))
    (incrementsOriginalParameterPoint y,incrementsOriginalSourcePoint y) hy.1 hW
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_meanError_coordinates
