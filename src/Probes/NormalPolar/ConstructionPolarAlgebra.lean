import NormalPolar.ConstructionProjectorAlgebra
import NormalPolar.ConstructionInverseSqrtAlgebra

/-!
The explicit ambient orthogonal transport built from two genuine projections.
The same transport restricts to the normal-space identification in the next
file. Its restriction followed by the new projection is `actualPolarOperator`.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def actualAmbientPolar (P R : V →L[ℝ] V) : V →L[ℝ] V :=
  actualInvSqrt (projectionDefect P R) * projectionComparison P R

theorem actualInvSqrt_projection_commute_left (P R : V →L[ℝ] V)
    (hP : P * P = P) (hR : R * R = R) :
    Commute (actualInvSqrt (projectionDefect P R)) P :=
  actualInvSqrt_commute _ _ (projectionDefect_commute_left P R hP hR)

theorem actualInvSqrt_projection_commute_right (P R : V →L[ℝ] V)
    (hP : P * P = P) (hR : R * R = R) :
    Commute (actualInvSqrt (projectionDefect P R)) R :=
  actualInvSqrt_commute _ _ (projectionDefect_commute_right P R hP hR)

theorem actualInvSqrt_projectionComparison_commute (P R : V →L[ℝ] V)
    (hP : P * P = P) (hR : R * R = R) :
    Commute (actualInvSqrt (projectionDefect P R)) (projectionComparison P R) := by
  have hp := actualInvSqrt_projection_commute_left P R hP hR
  have hr := actualInvSqrt_projection_commute_right P R hP hR
  exact (hp.mul_right hr).add_right (((Commute.one_right _).sub_right hp).mul_right
    ((Commute.one_right _).sub_right hr))

theorem star_actualAmbientPolar (P R : V →L[ℝ] V)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) :
    star (actualAmbientPolar P R) =
      projectionComparison R P * actualInvSqrt (projectionDefect P R) := by
  rw [actualAmbientPolar, star_mul, star_projectionComparison P R hP hR,
    (actualInvSqrt_selfAdjoint _ (projectionDefect_selfAdjoint P R hP hR)).star_eq]

theorem actualAmbientPolar_mul_star (P R : V →L[ℝ] V)
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hclose : ‖P - R‖ < 1) :
    actualAmbientPolar P R * star (actualAmbientPolar P R) = 1 := by
  have hS := actualInvSqrt_mul_self_one_sub (projectionDefect P R)
    (norm_sub_sq_lt_one P R hclose)
  have hcomm := (Commute.one_right (actualInvSqrt (projectionDefect P R))).sub_right
    (actualInvSqrt_commute (projectionDefect P R) _ (Commute.refl _))
  rw [star_actualAmbientPolar P R hP.isSelfAdjoint hR.isSelfAdjoint, actualAmbientPolar]
  calc
    _ = actualInvSqrt (projectionDefect P R) *
        ((projectionComparison P R * projectionComparison R P) *
          actualInvSqrt (projectionDefect P R)) := by simp only [mul_assoc]
    _ = actualInvSqrt (projectionDefect P R) *
        ((1 - projectionDefect P R) * actualInvSqrt (projectionDefect P R)) := by
      rw [projectionComparison_mul_swap P R hP.isIdempotentElem hR.isIdempotentElem]
    _ = actualInvSqrt (projectionDefect P R) *
        (actualInvSqrt (projectionDefect P R) * (1 - projectionDefect P R)) := by
      rw [← hcomm.eq]
    _ = 1 := by simpa only [mul_assoc] using hS

theorem actualAmbientPolar_star_mul (P R : V →L[ℝ] V)
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hclose : ‖P - R‖ < 1) :
    star (actualAmbientPolar P R) * actualAmbientPolar P R = 1 := by
  have hS := actualInvSqrt_mul_self_one_sub (projectionDefect P R)
    (norm_sub_sq_lt_one P R hclose)
  have hcomm : Commute (actualInvSqrt (projectionDefect P R)) (projectionComparison R P) := by
    simpa only [projectionDefect_swap] using
      actualInvSqrt_projectionComparison_commute R P hR.isIdempotentElem hP.isIdempotentElem
  rw [star_actualAmbientPolar P R hP.isSelfAdjoint hR.isSelfAdjoint, actualAmbientPolar]
  calc
    _ = (actualInvSqrt (projectionDefect P R) * actualInvSqrt (projectionDefect P R)) *
        (projectionComparison R P * projectionComparison P R) := by
      rw [hcomm.symm.eq, mul_assoc, ← mul_assoc (projectionComparison R P), hcomm.symm.eq]
      simp only [mul_assoc]
    _ = (actualInvSqrt (projectionDefect P R) * actualInvSqrt (projectionDefect P R)) *
        (1 - projectionDefect P R) := by
      rw [projectionComparison_swap_mul P R hP.isIdempotentElem hR.isIdempotentElem]
    _ = 1 := hS

theorem actualAmbientPolar_mul_new (P R : V →L[ℝ] V)
    (hR : R * R = R) :
    actualAmbientPolar P R * R = actualPolarOperator P R := by
  rw [actualAmbientPolar, mul_assoc, projectionComparison_mul_new P R hR]
  rfl

theorem actualAmbientPolar_intertwine (P R : V →L[ℝ] V)
    (hP : P * P = P) (hR : R * R = R) :
    actualAmbientPolar P R * R = P * actualAmbientPolar P R := by
  unfold actualAmbientPolar
  rw [mul_assoc, projectionComparison_intertwine P R hP hR, ← mul_assoc,
    (actualInvSqrt_projection_commute_left P R hP hR).eq, mul_assoc]

theorem actualAmbientPolar_star_intertwine (P R : V →L[ℝ] V)
    (hP : IsStarProjection P) (hR : IsStarProjection R) :
    R * star (actualAmbientPolar P R) = star (actualAmbientPolar P R) * P := by
  have h := congrArg star (actualAmbientPolar_intertwine P R hP.isIdempotentElem hR.isIdempotentElem)
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using h

end GlobalEmbedding.NormalPolar
