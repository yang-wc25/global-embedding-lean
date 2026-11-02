import Smoothing.WeightedActualOperations
import Smoothing.ParameterGeometryJets

/-!
# Native coordinate metric pairing for actual displacements

The output is a genuine continuous bilinear form with its native operator
norm. Its inputs are the actual spatial derivatives. This fixed bilinear
operator has norm at most one, so no coordinate-cardinality replacement or
changed norm enters the metric remainder estimate.
-/

noncomputable section
open Set
open scoped ContDiff

namespace GlobalEmbedding.Continuation

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Cache only native operator structures, with their original norms.
private noncomputable local instance metricTensorSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricTensorNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance metricTensorSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance metricPartialPairingSemi :
    SeminormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance metricPartialPairingNormed :
    NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance metricPartialPairingSpace :
    NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual tensor `(v,w) ↦ ⟪A v,B w⟫` as a fixed native continuous
bilinear operator in the two spatial derivative inputs. -/
def actualMetricJetPairing :
    (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.precompL D (ContinuousLinearMap.precompR D (innerSL ℝ))

@[simp] theorem actualMetricJetPairing_apply
    (A B : D →L[ℝ] V) (v w : D) :
    actualMetricJetPairing A B v w = inner ℝ (A v) (B w) := rfl

theorem actualMetricJetPairing_norm_le :
    ‖actualMetricJetPairing (D := D) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro B
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  calc
    ‖actualMetricJetPairing A B v w‖ = ‖inner ℝ (A v) (B w)‖ := rfl
    _ ≤ ‖A v‖ * ‖B w‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖v‖) * (‖B‖ * ‖w‖) :=
      mul_le_mul (A.le_opNorm v) (B.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = 1 * ‖A‖ * ‖B‖ * ‖v‖ * ‖w‖ := by ring

/-- This is the literal quadratic metric tensor of a native spatial jet. -/
def actualSpatialMetric (A : D →L[ℝ] V) : D →L[ℝ] D →L[ℝ] ℝ :=
  actualMetricJetPairing A A

@[simp] theorem actualSpatialMetric_apply (A : D →L[ℝ] V) (v w : D) :
    actualSpatialMetric A v w = inner ℝ (A v) (A w) := rfl

/-- Exact cross/self expansion for the SAME two actual spatial derivatives. -/
theorem actualSpatialMetric_add_sub (A B : D →L[ℝ] V) :
    actualSpatialMetric (A + B) - actualSpatialMetric A =
      actualMetricJetPairing A B + actualMetricJetPairing B A + actualSpatialMetric B := by
  simp only [actualSpatialMetric, map_add, ContinuousLinearMap.add_apply]
  abel

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualMetricJetPairing_norm_le
#print axioms GlobalEmbedding.Continuation.actualSpatialMetric_add_sub
