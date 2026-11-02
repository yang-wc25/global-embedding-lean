import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Actual pointwise bounded bilinear lifting to uniform-norm function spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `bounded-continuous-bilinear-lift`.
-/

open scoped BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- Lift a genuine bounded bilinear map pointwise to actual bounded continuous functions.

Actual bilinear continuity makes p↦B(f(p),g(p)) continuous. Its original pointwise norm is
bounded by norm(B) norm(f) norm(g), hence it is an actual bounded continuous function.
Pointwise linearity supplies the actual bilinear linear map; the original uniform bound
then makes it genuinely continuous in both uniform norms. Source: uniform auxiliary-parameter
contraction in the proof of `lem:balanced`, expanded on actual bounded-family Banach spaces. -/
noncomputable def boundedContinuousBilinearLift
    {P X Y Z : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : X →L[ℝ] Y →L[ℝ] Z) : (P →ᵇ X) →L[ℝ] (P →ᵇ Y) →L[ℝ] (P →ᵇ Z) := by
  let value (f : P →ᵇ X) (g : P →ᵇ Y) : P →ᵇ Z :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun p ↦ B (f p) (g p))
      ((B.continuous.comp f.continuous).clm_apply g.continuous)
      (‖B‖ * ‖f‖ * ‖g‖)
      (fun p ↦ B.le_of_opNorm₂_le_of_le le_rfl (f.norm_coe_le_norm p) (g.norm_coe_le_norm p))
  let linear : (P →ᵇ X) →ₗ[ℝ] (P →ᵇ Y) →ₗ[ℝ] (P →ᵇ Z) :=
    LinearMap.mk₂ ℝ value
      (by
        intro f₁ f₂ g
        ext p
        change B (f₁ p + f₂ p) (g p) = B (f₁ p) (g p) + B (f₂ p) (g p)
        simp)
      (by
        intro c f g
        ext p
        change B (c • f p) (g p) = c • B (f p) (g p)
        simp)
      (by
        intro f g₁ g₂
        ext p
        change B (f p) (g₁ p + g₂ p) = B (f p) (g₁ p) + B (f p) (g₂ p)
        simp)
      (by
        intro c f g
        ext p
        change B (f p) (c • g p) = c • B (f p) (g p)
        simp)
  exact linear.mkContinuous₂ ‖B‖ (fun f g ↦
    (BoundedContinuousFunction.norm_le (by positivity)).mpr
      (fun p ↦ B.le_of_opNorm₂_le_of_le le_rfl (f.norm_coe_le_norm p) (g.norm_coe_le_norm p)))

#print axioms boundedContinuousBilinearLift

end GlobalEmbedding.Paper
