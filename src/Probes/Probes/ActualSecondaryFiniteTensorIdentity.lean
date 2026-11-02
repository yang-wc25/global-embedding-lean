import Probes.ActualSecondaryFiniteCancellation
import Probes.ActualSecondaryTensorNaturality

/-!
# Exact native tensor identity for the full finite increment

The error is the metric of the literal same `F + U1 + U2` minus the original
metric and target tensor. The mean is extracted from the genuine physical
primary coefficients. Every nonzero ordered four-branch forcing remains in
the secondary error. The identity exposes precisely the four terms needed
for the original finite increment estimate.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def actualPrimaryJointWave
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
    (P Q : Label → Ep → Sub → D → V) : X → V :=
  fun z => incrementsPrimaryWave (fun nu => phi nu z.1) tau
    (fun nu => chi nu z.1) (fun nu => P nu z.1) (fun nu => Q nu z.1) z.2

def actualPrimaryOppositeMeanTensor
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
    (P Q : Label → Ep → Sub → D → V) : X → Tensor :=
  fun z => actualRealTensorAssembly (fun i j => incrementsOppositePrimaryContribution
    (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
      (fun a _ => EuclideanSpace.single a 1) z) i j)

def actualSecondaryForcingTensor
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
    (P Q : Label → Ep → Sub → D → V) (r : (Label × Label) × Fin 4) : X → Tensor :=
  fun z => actualRealTensorAssembly (fun i j =>
    incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2 z / tau) *
      incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun a _ => EuclideanSpace.single a 1) r.1.1 r.1.2 r.2 z i j)

def actualJointMetricLinearization (F U : X → V) : X → Tensor :=
  fun z => actualCoordinateMetricLinearization (fun x => F (z.1,x)) (fun x => U (z.1,x)) z.2

def actualFiniteMetricError (F U : X → V) (H : X → Tensor) (delta : ℝ) : X → Tensor :=
  fun z => actualSpatialMetric (fderiv ℝ (fun x => F (z.1,x) + U (z.1,x)) z.2) -
    actualSpatialMetric (fderiv ℝ (fun x => F (z.1,x)) z.2) - delta ^ 2 • H z

theorem actual_primary_secondary_native_tensor_identity
    (F : X → V) (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → Sub → D → ℝ) (P Q : Label → Ep → Sub → D → V)
    (secondary : Label → Label → Fin 4 → X → V) (H : X → Tensor) (delta : ℝ) (z : X)
    (hF : DifferentiableAt ℝ (fun x => F (z.1,x)) z.2)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2)
    (hsecondary : ∀ r ∈ actualSecondaryNonzeroRecords Label,
      DifferentiableAt ℝ (fun x => secondary r.1.1 r.1.2 r.2 (z.1,x)) z.2) :
    let U1 := actualPrimaryJointWave phi tau chi P Q
    let U2 := actualSecondaryNonzeroSum secondary
    actualFiniteMetricError F (fun y => U1 y + U2 y) H delta z =
      actualJointMetricLinearization F U1 z +
      (∑ r ∈ actualSecondaryNonzeroRecords Label,
        (actualJointMetricLinearization F (secondary r.1.1 r.1.2 r.2) z -
          actualSecondaryForcingTensor phi tau chi P Q r z)) +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x) + U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta ^ 2 • H z) := by
  intro U1 U2
  have hU1 : DifferentiableAt ℝ (fun x => U1 (z.1,x)) z.2 :=
    actual_primary_wave_differentiableAt (fun nu => phi nu z.1) tau (fun nu => chi nu z.1)
      (fun nu => P nu z.1) (fun nu => Q nu z.1) z.2 hphi hchi hP hQ
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  have hh := actual_primary_secondary_finite_metric_identity F phi tau chi P Q secondary z hF
    hphi hchi hP hQ hsecondary i j
  dsimp only at hh
  have hsum : (∑ r ∈ actualSecondaryNonzeroRecords Label,
      (actualJointMetricLinearization F (secondary r.1.1 r.1.2 r.2) z -
        actualSecondaryForcingTensor phi tau chi P Q r z)
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
    ∑ r ∈ actualSecondaryNonzeroRecords Label,
      (incrementsCoordinateMetricVariation (fun x => F (z.1,x))
        (fun x => secondary r.1.1 r.1.2 r.2 (z.1,x)) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
        (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2 z / tau) *
          incrementsSecondaryQuadraticForcing phi tau chi P Q
            (fun a _ => EuclideanSpace.single a 1) r.1.1 r.1.2 r.2 z i j).re) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [sub_apply, actualSecondaryForcingTensor, actualRealTensorAssembly_basis,
      actualJointMetricLinearization]
    rw [actual_coordinate_metric_linearization_eq_variation _ _ _ _ _ hF (hsecondary r hr)]
  simp only [actualFiniteMetricError, actualJointMetricLinearization, actualPrimaryOppositeMeanTensor,
    sub_apply, add_apply, sum_apply, smul_apply, smul_eq_mul, actualRealTensorAssembly_basis]
  rw [actual_coordinate_metric_linearization_eq_variation _ _ _ _ _ hF hU1]
  have hsum' := hsum
  simp only [actualJointMetricLinearization, sub_apply] at hsum'
  rw [hsum']
  have hAssoc : (fun x => F (z.1,x) + (U1 (z.1,x) + U2 (z.1,x))) =
      (fun x => F (z.1,x) + U1 (z.1,x) + U2 (z.1,x)) := by funext x; abel
  rw [hAssoc]
  dsimp only [U1, U2, actualPrimaryJointWave]
  simp only [sub_apply] at hh
  linarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_secondary_native_tensor_identity
