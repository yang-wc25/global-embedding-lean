import Probes.ActualSecondaryMetricRemainder
import Probes.ActualSecondarySupportedSum

/-!
# Exact metric calculus for the same actual finite increment

The metric and its first variation are the original induced metric and its
literal scalar derivative. The equalities below keep the same primary and
secondary displacements and both cross terms. They form the exact algebraic
consumer of the original nonzero quadratic forcing identity.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {n N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_coordinate_metric_jet_eq_induced
    (F : D → V) (x v w : D) :
    actualSpatialMetric (fderiv ℝ F x) v w =
      inducedMetric (I := 𝓘(ℝ, D)) F x
        ((tangentSpaceCastModel 𝓘(ℝ, D) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, D) x).symm w) := by
  rw [inducedMetric_apply, mfderiv_eq_fderiv]
  rfl

theorem actual_coordinate_metric_variation_eq
    (F Z : D → V) (x v w : D)
    (hF : DifferentiableAt ℝ F x) (hZ : DifferentiableAt ℝ Z x) :
    incrementsCoordinateMetricVariation F Z x v w =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ Z x w) +
        inner ℝ (fderiv ℝ Z x v) (fderiv ℝ F x w) :=
  (increments_inducedMetric_hasDerivAt F Z x v w hF hZ).deriv

theorem actual_coordinate_metric_variation_sum
    {A : Type*} (s : Finset A) (F : D → V) (Z : A → D → V) (x v w : D)
    (hF : DifferentiableAt ℝ F x)
    (hZ : ∀ a ∈ s, DifferentiableAt ℝ (Z a) x) :
    incrementsCoordinateMetricVariation F (fun y => ∑ a ∈ s, Z a y) x v w =
      ∑ a ∈ s, incrementsCoordinateMetricVariation F (Z a) x v w := by
  have hsum : DifferentiableAt ℝ (fun y => ∑ a ∈ s, Z a y) x := by
    exact DifferentiableAt.fun_sum hZ
  rw [actual_coordinate_metric_variation_eq F _ x v w hF hsum,
    fderiv_fun_sum hZ]
  simp only [sum_apply, inner_sum, sum_inner, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact (actual_coordinate_metric_variation_eq F (Z a) x v w hF (hZ a ha)).symm

/-- Literal primary finite waves are differentiable from their actual
phase, cutoff and two amplitude fields. -/
theorem actual_primary_wave_differentiableAt
    {Label Sub : Type*} [Fintype Label] [Fintype Sub]
    (phi : Label → D → ℝ) (tau : ℝ) (chi : Label → Sub → D → ℝ)
    (P Q : Label → Sub → D → V) (x : D)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu) x)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu a) x)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu a) x)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu a) x) :
    DifferentiableAt ℝ (incrementsPrimaryWave phi tau chi P Q) x := by
  let W := fun nu a y => WithLp.toLp 2 (fun c : Fin N =>
    (Complex.exp (((phi nu y / tau : ℝ) : ℂ) * Complex.I) *
      ((P nu a y c : ℂ) + Complex.I * (Q nu a y c : ℂ))).re)
  have hW (nu) (a) : DifferentiableAt ℝ (W nu a) x := by
    dsimp only [W]
    rw [increments_primary_real_mode_eq]
    have ht : DifferentiableAt ℝ (fun y => phi nu y / tau) x := by
      have hh := (hphi nu).const_smul tau⁻¹
      change DifferentiableAt ℝ (fun y => tau⁻¹ * phi nu y) x at hh
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have hc : DifferentiableAt ℝ (fun y => Real.cos (phi nu y / tau)) x :=
      ht.cos
    have hs : DifferentiableAt ℝ (fun y => Real.sin (phi nu y / tau)) x :=
      ht.sin
    exact ((hc.hasFDerivAt.smul (hP nu a).hasFDerivAt).sub
      (hs.hasFDerivAt.smul (hQ nu a).hasFDerivAt)).differentiableAt
  have hd (nu) (a) := (hchi nu a).hasFDerivAt.smul (hW nu a).hasFDerivAt
  have ht := HasFDerivAt.fun_sum (u := Finset.univ) fun nu _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => hd nu a
  exact ht.differentiableAt

/-- Exact metric split for one primary and one secondary displacement.
The remainder is the literal SAME-map metric difference proved quantitatively
in `actual_secondary_metric_remainder_weighted_jets`. -/
theorem actual_metric_increment_primary_secondary_split
    (F U W : D → V) (x v w : D)
    (hF : DifferentiableAt ℝ F x) (hU : DifferentiableAt ℝ U x)
    (hW : DifferentiableAt ℝ W x) :
    actualSpatialMetric (fderiv ℝ (fun y => F y + U y + W y) x) v w -
        actualSpatialMetric (fderiv ℝ F x) v w =
      incrementsCoordinateMetricVariation F U x v w +
      incrementsCoordinateMetricVariation F W x v w +
      actualSpatialMetric (fderiv ℝ U x) v w +
      (actualSpatialMetric (fderiv ℝ (fun y => U y + W y) x) -
        actualSpatialMetric (fderiv ℝ U x)) v w := by
  rw [actual_coordinate_metric_variation_eq F U x v w hF hU,
    actual_coordinate_metric_variation_eq F W x v w hF hW]
  have hd := ((hF.hasFDerivAt.fun_add hU.hasFDerivAt).fun_add hW.hasFDerivAt).fderiv
  have hu := (hU.hasFDerivAt.fun_add hW.hasFDerivAt).fderiv
  rw [hd, hu]
  simp only [actualSpatialMetric_apply, sub_apply, add_apply, inner_add_left, inner_add_right]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_coordinate_metric_jet_eq_induced
#print axioms GlobalEmbedding.Continuation.actual_coordinate_metric_variation_sum
#print axioms GlobalEmbedding.Continuation.actual_primary_wave_differentiableAt
#print axioms GlobalEmbedding.Continuation.actual_metric_increment_primary_secondary_split
