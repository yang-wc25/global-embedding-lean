import NormalPolar.ActualProbeInitialSupplySignedSecondaryResponses
import NormalPolar.JointMixedParameterInitialization

/-! The secondary response already proved on the original larger chart
ball holds on the ball chosen during initialization. The source function,
parameter map, charts, Q and original spatial norms remain literally the same. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem actualProbeInitialSecondaryBallBounds_smallBuffer
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin (m+1))))
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin (m+1))))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (C t : ℝ) (wave : P × M → EuclideanSpace ℝ (Fin N))
    (cap : ℝ) (hcap : 0 < cap)
    (hbound : actualProbeInitialSecondaryBallBounds A Omega B C t wave) :
    actualProbeInitialSecondaryBallBounds A Omega (passiveOriginalSmallBuffer B cap hcap) C t wave := by
  have hradius : actualRepairParameterRadius
      (tensorChartFamilyOfAtlas (passiveOriginalSmallBuffer B cap hcap)) ≤
      actualRepairParameterRadius (tensorChartFamilyOfAtlas B) := by
    change min B.buffer cap / _ ≤ B.buffer / _
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
  have hball := Metric.ball_subset_ball (x := (0 : Fin d → ℝ)) hradius
  intro b p₀ hp₀ ball S
  have hb := hbound b p₀ hp₀
  refine ⟨fun i => (hb.1 i).mono (Set.prod_mono hball Subset.rfl),?_,?_⟩
  · intro i v hv y hy direction
    exact hb.2.1 i v (hball hv) y hy direction
  · intro v direction hv
    exact hb.2.2 v direction (hball hv)

theorem actualProbeInitialSecondaryBallBounds_initialized
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin (m+1))))
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin (m+1))))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (C t : ℝ) (wave : P × M → EuclideanSpace ℝ (Fin N))
    (sourceCost rho : ℝ) (hrho : 0 < rho)
    (hbound : actualProbeInitialSecondaryBallBounds A Omega B C t wave) :
    actualProbeInitialSecondaryBallBounds A Omega
      (jointMixedParameterInitializedAtlas B sourceCost rho hrho) C t wave :=
  actualProbeInitialSecondaryBallBounds_smallBuffer A Omega B C t wave _
    (div_pos (passiveOriginalReserveAmplitude_pos sourceCost rho hrho) (by positivity)) hbound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSecondaryBallBounds_smallBuffer
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSecondaryBallBounds_initialized
