import NormalPolar.ActualProbeFirstModelBounds
import Main.GeneralLegalWaveRefinement

/-! The four parameter conclusions for one concrete first map at one scale.
This is an output proposition used by the primitive factories, with the
same literal G in every derivative and every original atlas gauge. -/
noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
variable {n N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)
private local instance fourFieldsHessianSemi : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance fourFieldsHessianNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance fourFieldsHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

def GeneralWaveFirstFourAt
    (F₀ : M→V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀) (waves : Fin r→OpenSupportedLegalWave F₀ hF₀)
    (A : BufferedAtlas M E) (weight : Fin r→ℝ) (G : ProbeParameters r→M→V)
    (U : Set (ProbeParameters r)) (radius t C etaH etaV : ℝ) : Prop :=
  ∀ u∈U, ‖u‖<radius →
    (∀ direction, probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => G v x) u direction)≤
      ENNReal.ofReal (C*t^(10:ℕ)*‖direction‖)) ∧
    (∀ direction, probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => G v x) u direction)≤
      ENNReal.ofReal (C*t^((44:ℝ)/5)*‖direction‖)) ∧
    (∀ l sine i x, x∈A.support i →
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (G v∘(A.chart i).symm)) (A.chart i x)) u (Pi.single (l,sine) 1)-
        (t^((44:ℝ)/5)*probeTrig sine (weight l*(waves l).phase x/t^((6:ℝ)/5))) •
          phaseRankOneHessian ((waves l).phase∘(A.chart i).symm) ((waves l).value∘(A.chart i).symm) (A.chart i x)‖≤
        t^((44:ℝ)/5)*(etaH+C*‖u‖)) ∧
    (∀ l sine x,
      ‖fderiv ℝ (fun v => G v x) u (Pi.single (l,sine) 1)-
        (-(t^((56:ℝ)/5))*(weight l^2)⁻¹*probeTrig sine (weight l*(waves l).phase x/t^((6:ℝ)/5))) • (waves l).value x‖≤
        t^((56:ℝ)/5)*(etaV+C*‖u‖))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralWaveFirstFourAt
