import Probes.ActualSecondaryCompleteMetricIdentity
import Probes.ActualSecondaryGroupedQuadratic

/-!
# Exact metric error using the original grouped derivative

The native quadratic forcing is recovered by actual inverse chart transport
and the ordinary partition. This identifies the complete metric error with
its four literal terms: primary linear residual, constructed secondary
physical residual, actual cross/self metric difference, and actual mean
defect. No inactive phase derivative is assumed. The true original grouped derivative
is supplied by the original-family binding from local primitive conditions.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep Label SubPrimary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_primary_quadratic_native_tensor_identity_of_grouped
    (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (z : X)
    (hgrouped : ∀ i, fderiv ℝ
      (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2 (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
          (fun r _ => EuclideanSpace.single r 1) z) i) :
    actualSpatialMetric (fderiv ℝ (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2) +
      (∑ r ∈ actualSecondaryNonzeroRecords Label, actualSecondaryForcingTensor phi tau chi P Q r z) =
        actualPrimaryOppositeMeanTensor phi tau chi P Q z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  have hh := actual_secondary_quadratic_grouped_identity phi tau chi P Q
    (fun a _ => EuclideanSpace.single a 1) z i j
  dsimp only at hh
  rw [← hgrouped i, ← hgrouped j] at hh
  have heq := congrFun (actualSecondaryNonzeroSum_eq_record_sum (fun nu mu q w =>
    (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q w / tau) *
      incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun a _ => EuclideanSpace.single a 1) nu mu q w i j).re)) z
  simp only [actualSecondaryNonzeroSum] at heq
  rw [heq] at hh
  simp only [actualPrimaryJointWave] at hh
  simp only [actualPrimaryJointWave, actualSecondaryForcingTensor, actualPrimaryOppositeMeanTensor,
    add_apply, sum_apply, actualRealTensorAssembly_basis, actualSpatialMetric_apply]
  linarith

 theorem actual_primary_secondary_native_grouped_identity_of_grouped
    (F U2 : X → V) (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (H : X → Tensor) (delta : ℝ) (z : X)
    (hF : DifferentiableAt ℝ (fun x => F (z.1,x)) z.2)
    (hU2 : DifferentiableAt ℝ (fun x => U2 (z.1,x)) z.2)
    (hU1 : DifferentiableAt ℝ
      (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2)
    (hgrouped : ∀ i, fderiv ℝ
      (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2 (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
          (fun r _ => EuclideanSpace.single r 1) z) i) :
    let U1 := actualPrimaryJointWave phi tau chi P Q
    actualFiniteMetricError F (fun y => U1 y + U2 y) H delta z =
      actualJointMetricLinearization F U1 z +
      (actualJointMetricLinearization F U2 z -
        ∑ r ∈ actualSecondaryNonzeroRecords Label, actualSecondaryForcingTensor phi tau chi P Q r z) +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x) + U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta ^ 2 • H z) := by
  intro U1
  change DifferentiableAt ℝ (fun x => U1 (z.1,x)) z.2 at hU1
  have hquad := actual_primary_quadratic_native_tensor_identity_of_grouped phi tau chi P Q z hgrouped
  have hsum := (hU1.hasFDerivAt.fun_add hU2.hasFDerivAt).fderiv
  have htotal := (hF.hasFDerivAt.fun_add (hU1.hasFDerivAt.fun_add hU2.hasFDerivAt)).fderiv
  ext v w
  have hq := congrArg (fun T : Tensor => T v w) hquad
  simp only [add_apply] at hq
  simp only [actualFiniteMetricError, actualJointMetricLinearization,
    actualCoordinateMetricLinearization_apply, sub_apply, add_apply, smul_apply,
    smul_eq_mul, htotal, hsum, actualSpatialMetric_apply, inner_add_left, inner_add_right]
  dsimp only [U1] at hq ⊢
  simp only [actualSpatialMetric_apply] at hq
  linarith

variable {M SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype SubSecondary]
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_constructed_complete_metric_identity_of_grouped
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (length : ℕ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (binding : ∀ r : ActualSecondarySignedRecord Label,
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) r.1.1.1 r.1.1.2 r.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.1.1.1 r.1.1.2 r.1.2))
    (H : X → Tensor) (hW : IsOpen W)
    (Omega : Set X) (hOmega : IsOpen Omega) (hOmegaB : Omega ⊆ b.target)
    (hb : ContMDiffOn 𝓘(ℝ, X) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ b.symm Omega)
    (hmap : MapsTo b.symm Omega W) (z : X) (hz : z ∈ Omega)
    (hFobs : DifferentiableAt ℝ (fun x => F (b.symm (z.1,x)).1 (b.symm (z.1,x)).2) z.2)
    (hU1 : DifferentiableAt ℝ
      (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2)
    (hgrouped : ∀ i, fderiv ℝ
      (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2 (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
          (fun r _ => EuclideanSpace.single r 1) z) i) :
    let Fobs := fun y : X => F (b.symm y).1 (b.symm y).2
    let U1 := actualPrimaryJointWave phi tau chi P Q
    let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ b.symm
    actualFiniteMetricError Fobs (fun y => U1 y + U2 y) H delta z =
      actualJointMetricLinearization Fobs U1 z +
      actualConstructedSecondaryPhysicalSum F hF data b.symm tau length z +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x) + U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta ^ 2 • H z) := by
  intro Fobs U1 U2
  have hU2 := actual_constructed_secondary_observed_differentiableAt F hF data tau length hW
    b.symm Omega hOmega hb hmap z hz
  have heq := actual_primary_secondary_native_grouped_identity_of_grouped Fobs U2 phi tau chi P Q H delta z
    hFobs hU2 hU1 hgrouped
  have hforce := actual_constructed_secondary_original_forcing_sum F hF data b phi tau chi P Q binding z
    (hOmegaB hz) (hmap hz)
  rw [← hforce] at heq
  have hcancel := actual_constructed_secondary_linearized_cancellation F hF n j ell Mg CH delta W data
    tau length hW b.symm Omega hOmega hb hmap z hz
  change actualJointMetricLinearization Fobs U2 z -
    actualConstructedSecondaryForcingSum F hF data b.symm tau z = _ at hcancel
  rw [hcancel] at heq
  exact heq

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_primary_quadratic_native_tensor_identity_of_grouped
#print axioms GlobalEmbedding.Continuation.actual_primary_secondary_native_grouped_identity_of_grouped
#print axioms GlobalEmbedding.Continuation.actual_constructed_complete_metric_identity_of_grouped
