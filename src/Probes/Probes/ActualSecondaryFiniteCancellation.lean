import Probes.ActualSecondaryMetricIdentity
import Probes.ActualSecondaryFamily

/-!
# Exact cancellation for the full actual finite primary/secondary increment

The original four signed branches and every ordered label pair are retained.
The original negative quadratic forcing cancels the nonzero quadratic part
of the SAME literal primary wave. The resulting metric identity separates
only the actual primary linear residual, the actual secondary linear
residual sum, and the actual secondary cross/self metric remainder.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

def actualSecondaryNonzeroRecords (Label : Type*) [Fintype Label] [DecidableEq Label] :
    Finset ((Label × Label) × Fin 4) :=
  Finset.univ.filter fun r => r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3

theorem actualSecondaryNonzeroSum_eq_record_sum
    {Label X Y : Type*} [Fintype Label] [DecidableEq Label]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (W : Label → Label → Fin 4 → X → Y) :
    actualSecondaryNonzeroSum W = fun z => ∑ r ∈ actualSecondaryNonzeroRecords Label,
      W r.1.1 r.1.2 r.2 z := by
  funext z
  simp only [actualSecondaryNonzeroSum, actualSecondaryNonzeroRecords,
    Finset.sum_filter, Fintype.sum_prod_type]

variable {m N : ℕ} {Ep Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Exact original finite cancellation, on the same observation coordinates.
Every secondary error is its literal physical metric variation minus the
original modulated forcing. Thus this identity applies directly to the
supported actual secondary family after its true chart transport. -/
theorem actual_primary_secondary_finite_metric_identity
    (F : X → V) (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → Sub → D → ℝ) (P Q : Label → Ep → Sub → D → V)
    (secondary : Label → Label → Fin 4 → X → V) (z : X)
    (hF : DifferentiableAt ℝ (fun x => F (z.1, x)) z.2)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2)
    (hsecondary : ∀ r ∈ actualSecondaryNonzeroRecords Label,
      DifferentiableAt ℝ (fun x => secondary r.1.1 r.1.2 r.2 (z.1, x)) z.2)
    (i j : Fin (m + 1)) :
    let U1 := incrementsPrimaryWave (fun nu => phi nu z.1) tau
      (fun nu => chi nu z.1) (fun nu => P nu z.1) (fun nu => Q nu z.1)
    let U2 := fun x => actualSecondaryNonzeroSum secondary (z.1, x)
    let coeff := incrementsSecondaryPhysicalCoefficient phi tau chi P Q
      (fun a _ => EuclideanSpace.single a 1) z
    let mean := (incrementsOppositePrimaryContribution coeff i j).re
    let Esecondary : ℝ := (actualSecondaryNonzeroRecords Label).sum
      (fun r : (Label × Label) × Fin 4 =>
      incrementsCoordinateMetricVariation (fun x => F (z.1, x))
        (fun x => secondary r.1.1 r.1.2 r.2 (z.1, x)) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi r.1.1 r.1.2 r.2 z / tau) *
        incrementsSecondaryQuadraticForcing phi tau chi P Q
          (fun a _ => EuclideanSpace.single a 1) r.1.1 r.1.2 r.2 z i j).re)
    actualSpatialMetric (fderiv ℝ (fun x => F (z.1, x) + U1 x + U2 x) z.2)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      actualSpatialMetric (fderiv ℝ (fun x => F (z.1, x)) z.2)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) - mean =
      incrementsCoordinateMetricVariation (fun x => F (z.1, x)) U1 z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + Esecondary +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 x + U2 x) z.2) -
        actualSpatialMetric (fderiv ℝ U1 z.2))
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  intro U1 U2 coeff mean Esecondary
  have hU1 : DifferentiableAt ℝ U1 z.2 := actual_primary_wave_differentiableAt
    (fun nu => phi nu z.1) tau (fun nu => chi nu z.1)
    (fun nu => P nu z.1) (fun nu => Q nu z.1) z.2 hphi hchi hP hQ
  have hU2eq : U2 = fun x => ∑ r ∈ actualSecondaryNonzeroRecords Label,
      secondary r.1.1 r.1.2 r.2 (z.1, x) := by
    funext x
    exact congrFun (actualSecondaryNonzeroSum_eq_record_sum secondary) (z.1, x)
  have hU2 : DifferentiableAt ℝ U2 z.2 := by
    rw [hU2eq]
    exact DifferentiableAt.fun_sum hsecondary
  have hv := actual_coordinate_metric_variation_sum (actualSecondaryNonzeroRecords Label)
    (fun x => F (z.1, x)) (fun r x => secondary r.1.1 r.1.2 r.2 (z.1, x))
    z.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) hF hsecondary
  rw [← hU2eq] at hv
  let forcing := fun nu mu q (w : X) =>
    (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q w / tau) *
      incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun a _ => EuclideanSpace.single a 1) nu mu q w i j).re
  have hf0 := increments_secondary_quadratic_forcing_exact phi tau chi P Q
    (fun a _ => EuclideanSpace.single a 1) z hphi hchi hP hQ i j
  have hforce : (∑ r ∈ actualSecondaryNonzeroRecords Label, forcing r.1.1 r.1.2 r.2 z) =
      -actualSpatialMetric (fderiv ℝ U1 z.2) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + mean := by
    rw [← congrFun (actualSecondaryNonzeroSum_eq_record_sum forcing) z]
    exact hf0
  have hE : Esecondary = incrementsCoordinateMetricVariation (fun x => F (z.1, x)) U2 z.2
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      (-actualSpatialMetric (fderiv ℝ U1 z.2) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + mean) := by
    dsimp only [Esecondary]
    rw [Finset.sum_sub_distrib, ← hv]
    exact congrArg (fun t => incrementsCoordinateMetricVariation (fun x => F (z.1, x)) U2 z.2
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) - t) hforce
  have hs := actual_metric_increment_primary_secondary_split (fun x => F (z.1, x)) U1 U2 z.2
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) hF hU1 hU2
  linarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualSecondaryNonzeroSum_eq_record_sum
#print axioms GlobalEmbedding.Continuation.actual_primary_secondary_finite_metric_identity
