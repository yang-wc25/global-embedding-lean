import Probes.ActualSecondaryMetricIdentity
import Probes.ActualSecondaryTensorResidual

/-!
# Natural coordinate change of the actual linearized metric tensor

Both derivative slots of the induced-metric variation transform by the
actual derivative of the coordinate change. The zero-germ lemma applies to
the actual correction, so inactive supported pieces contribute no metric
variation in an observation chart. No support claim about a formal error
carrier is needed.
-/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {D E V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def actualCoordinateMetricLinearization (F U : D → V) (x : D) : D →L[ℝ] D →L[ℝ] ℝ :=
  actualMetricJetPairing (fderiv ℝ F x) (fderiv ℝ U x) +
    actualMetricJetPairing (fderiv ℝ U x) (fderiv ℝ F x)

@[simp] theorem actualCoordinateMetricLinearization_apply (F U : D → V) (x v w : D) :
    actualCoordinateMetricLinearization F U x v w =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ U x w) +
        inner ℝ (fderiv ℝ U x v) (fderiv ℝ F x w) := rfl

theorem actual_coordinate_metric_linearization_comp
    (F U : E → V) (phi : D → E) (x : D)
    (hF : DifferentiableAt ℝ F (phi x)) (hU : DifferentiableAt ℝ U (phi x))
    (hphi : DifferentiableAt ℝ phi x) :
    actualCoordinateMetricLinearization (F ∘ phi) (U ∘ phi) x =
      (actualCoordinateMetricLinearization F U (phi x)).bilinearComp
        (fderiv ℝ phi x) (fderiv ℝ phi x) := by
  ext v w
  simp only [actualCoordinateMetricLinearization_apply, fderiv_comp x hF hphi,
    fderiv_comp x hU hphi, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply]

theorem actual_coordinate_metric_linearization_zero_germ
    (F U : D → V) (x : D) (hU : U =ᶠ[𝓝 x] fun _ => 0) :
    actualCoordinateMetricLinearization F U x = 0 := by
  ext v w
  simp only [actualCoordinateMetricLinearization_apply, hU.fderiv_eq, fderiv_fun_const,
    Pi.zero_apply, zero_apply, inner_zero_right, inner_zero_left, add_zero]

theorem actual_coordinate_metric_linearization_eq_variation
    {n N : ℕ} (F U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F x) (hU : DifferentiableAt ℝ U x) :
    actualCoordinateMetricLinearization F U x v w =
      incrementsCoordinateMetricVariation F U x v w :=
  (actual_coordinate_metric_variation_eq F U x v w hF hU).symm

/-- Every ordered Euclidean basis entry determines the native tensor. -/
theorem actual_bilinear_tensor_eq_of_basis {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (h : ∀ i j, A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) : A = B := by
  have hv (v : EuclideanSpace ℝ (Fin n)) :
      (∑ i, v i • EuclideanSpace.single i 1) = v := by
    ext a
    simp [EuclideanSpace.single, Pi.single_apply]
  ext v w
  rw [← hv v, ← hv w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  simp only [h]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_coordinate_metric_linearization_comp
#print axioms GlobalEmbedding.Continuation.actual_coordinate_metric_linearization_zero_germ
#print axioms GlobalEmbedding.Continuation.actual_bilinear_tensor_eq_of_basis
