import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, uniform ellipticity and smooth matrix inversion.
This is the explicit coercive inverse prerequisite of the full inverse Cj estimate. -/

namespace GlobalEmbedding.Paper
open scoped ContDiff

/-- A coercive smooth field of finite-dimensional real endomorphisms has an actual
smooth inverse, with inverse norm at most the reciprocal coercivity constant.

Proof: Cauchy–Schwarz turns coercivity into c‖v‖≤‖Pv‖. Its kernel is zero;
finite dimension gives a continuous linear equivalence. Apply the same inequality
to the actual inverse value and take the operator norm. Smoothness follows locally
by composition with the smooth inversion map at each invertible operator.
Source: `prop:initialization` proof, line822; explicit inverse derivative line1401.
Empty U and zero-dimensional fibers are included. -/
theorem coercive_inverse_smooth_bound
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Set D) (hU : IsOpen U) (P : D → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hP : ContDiffOn ℝ ∞ P U)
    (hcoer : ∀ x ∈ U, ∀ v : E, c * ‖v‖ ^ 2 ≤ inner ℝ v (P x v)) :
    (∀ x ∈ U, (P x).IsInvertible ∧ ‖(P x).inverse‖ ≤ c⁻¹) ∧
      ContDiffOn ℝ ∞ (fun x ↦ (P x).inverse) U := by
  have hbase : ∀ x ∈ U, (P x).IsInvertible ∧ ‖(P x).inverse‖ ≤ c⁻¹ := by
    intro x hx
    have hbound : ∀ v : E, c * ‖v‖ ≤ ‖P x v‖ := by
      intro v
      by_cases hv : v = 0
      · simp [hv]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hi := (hcoer x hx v).trans (real_inner_le_norm v (P x v))
      nlinarith
    have hinj : Function.Injective (P x) := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      change (P x) v = 0 at hv
      have hb := hbound v
      rw [hv, norm_zero] at hb
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.mp this
    let e : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (P x).toLinearMap
        ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
    have hinv : (P x).IsInvertible := ⟨e, by ext v; rfl⟩
    refine ⟨hinv, ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) ?_⟩
    intro v
    have hb := hbound ((P x).inverse v)
    rw [hinv.self_apply_inverse] at hb
    exact (le_inv_mul_iff₀ hc).mpr hb
  refine ⟨hbase, ?_⟩
  intro x hx
  exact (((hbase x hx).1.contDiffAt_map_inverse).comp x
    (hP.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

end GlobalEmbedding.Paper
