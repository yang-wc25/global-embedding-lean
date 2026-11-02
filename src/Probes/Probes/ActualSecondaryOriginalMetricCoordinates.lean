import Probes.ActualSecondaryCompleteMetricJets
import Smoothing.ParameterRound2CrossCoordinates
import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-!
# Literal original tensor coordinates of the same finite metric error

The target is pulled back on the original source tangent vectors. The metric
terms are the same native F and U and use only source differentiation. The
full parameter coordinate remains present. The original ordered component
map and exact source-first model equivalence are preserved.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {m d N pcount : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance originalErrorTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance originalErrorTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance originalErrorTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 def actualOriginalNativeTargetTensor
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin pcount) (z : X) : Tensor :=
  parameterRound2_meanTensorAssembly (m+1) (fun ij =>
    (H ((B i.2).symm z.1) ((A.chart i.1).symm z.2)
      (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 ij.1)
      (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 ij.2) : ℂ))

 theorem actualOriginalNativeTargetTensor_basis
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin pcount) (z : X) (a b : Fin (m+1)) :
    actualOriginalNativeTargetTensor A B H i z (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
      H ((B i.2).symm z.1) ((A.chart i.1).symm z.2)
        (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 a)
        (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) z.2 b) := by
  rw [actualOriginalNativeTargetTensor, parameterRound2_meanTensorAssembly_basis, Complex.ofReal_re]

 def actualOriginalNativeMetricError
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (delta : ℝ)
    (i : Fin A.count × Fin pcount) : X → Tensor :=
  actualFiniteMetricError
    (fun z => F ((B i.2).symm z.1, (A.chart i.1).symm z.2))
    (fun z => U ((B i.2).symm z.1, (A.chart i.1).symm z.2))
    (actualOriginalNativeTargetTensor A B H i) delta

 theorem actual_original_metric_error_coordinates
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F U : P × M → V)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F (p,x)))
    (hU : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => U (p,x)))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta : ℝ) (i : Fin A.count × Fin pcount) (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) :
    incrementsOriginalTensorCoordinates A B (incrementsOriginalMetricError F U H delta) i y =
      parameterRound2_metricComponents (m+1)
        (actualOriginalNativeMetricError A B F U H delta i ((parameterTensorModelEquiv (m+1) d).symm y)) := by
  funext k
  let p := (B i.2).symm (incrementsOriginalParameterPoint y)
  let x := incrementsOriginalSourcePoint y
  let v := EuclideanSpace.single (finProdFinEquiv.symm k).1 (1 : ℝ)
  let w := EuclideanSpace.single (finProdFinEquiv.symm k).2 (1 : ℝ)
  have hFv := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)) (hF p) x hy.1 v
  have hFw := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)) (hF p) x hy.1 w
  have hSv := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)+U (p,x)) ((hF p).add (hU p)) x hy.1 v
  have hSw := parameterRound2_ambientDerivative_inverseChart_apply (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F (p,x)+U (p,x)) ((hF p).add (hU p)) x hy.1 w
  simp only [parameterRound2_metricComponents_apply, actualOriginalNativeMetricError,
    actualFiniteMetricError, sub_apply, smul_apply, smul_eq_mul, actualSpatialMetric_apply,
    actualOriginalNativeTargetTensor_basis]
  exact congrArg (fun t : ℝ => t - delta^2 * H p ((A.chart i.1).symm x)
    (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) x (finProdFinEquiv.symm k).1)
    (incrementsGlobalObservationVector (I := 𝓙) (A.chart i.1) x (finProdFinEquiv.symm k).2))
    (congrArg₂ (fun a b : ℝ => a-b)
      (congrArg₂ (fun a b : V => inner ℝ a b) hSv hSw)
      (congrArg₂ (fun a b : V => inner ℝ a b) hFv hFw))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_metric_error_coordinates
