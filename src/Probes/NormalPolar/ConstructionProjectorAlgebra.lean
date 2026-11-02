import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing

/-!
The algebra of the actual pair of orthogonal projections.  No identification,
square root, or closeness conclusion is assumed here.  These identities are
used with the explicit analytic inverse square root in `ConstructionPolar`.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar

section Ring
variable {A : Type*} [Ring A]

def projectionDefect (P R : A) : A := (P - R) ^ 2

def projectionComparison (P R : A) : A := P * R + (1 - P) * (1 - R)

theorem projection_mul_repeat (P : A) (hP : P * P = P) (a : A) :
    P * (P * a) = P * a := by
  rw [← mul_assoc, hP]

theorem projectionDefect_commute_left (P R : A)
    (hP : P * P = P) (hR : R * R = R) :
    Commute (projectionDefect P R) P := by
  unfold projectionDefect Commute SemiconjBy
  noncomm_ring [hP, hR, projection_mul_repeat P hP, projection_mul_repeat R hR]

theorem projectionDefect_commute_right (P R : A)
    (hP : P * P = P) (hR : R * R = R) :
    Commute (projectionDefect P R) R := by
  unfold projectionDefect Commute SemiconjBy
  noncomm_ring [hP, hR, projection_mul_repeat P hP, projection_mul_repeat R hR]

theorem projectionComparison_mul_new (P R : A)
    (hR : R * R = R) :
    projectionComparison P R * R = P * R := by
  unfold projectionComparison
  noncomm_ring [hR]

theorem old_mul_projectionComparison (P R : A)
    (hP : P * P = P) :
    P * projectionComparison P R = P * R := by
  unfold projectionComparison
  noncomm_ring [hP, projection_mul_repeat P hP]

theorem projectionComparison_intertwine (P R : A)
    (hP : P * P = P) (hR : R * R = R) :
    projectionComparison P R * R = P * projectionComparison P R := by
  rw [projectionComparison_mul_new P R hR, old_mul_projectionComparison P R hP]

theorem projectionComparison_mul_swap (P R : A)
    (hP : P * P = P) (hR : R * R = R) :
    projectionComparison P R * projectionComparison R P = 1 - projectionDefect P R := by
  unfold projectionComparison projectionDefect
  noncomm_ring [hP, hR, projection_mul_repeat P hP, projection_mul_repeat R hR]

theorem projectionDefect_swap (P R : A) : projectionDefect R P = projectionDefect P R := by
  unfold projectionDefect
  noncomm_ring

theorem projectionComparison_swap_mul (P R : A)
    (hP : P * P = P) (hR : R * R = R) :
    projectionComparison R P * projectionComparison P R = 1 - projectionDefect P R := by
  rw [projectionComparison_mul_swap R P hR hP, projectionDefect_swap]

end Ring

section Star
variable {A : Type*} [Ring A] [StarRing A]

theorem projectionDefect_selfAdjoint (P R : A)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (projectionDefect P R) := by
  exact (hP.sub hR).pow 2

theorem star_projectionComparison (P R : A)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) :
    star (projectionComparison P R) = projectionComparison R P := by
  simp only [projectionComparison, star_add, star_mul, star_sub, star_one, hP.star_eq, hR.star_eq]

end Star

end GlobalEmbedding.NormalPolar
