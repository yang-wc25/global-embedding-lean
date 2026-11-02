import NormalPolar.InverseSqrtSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
The explicit binomial series squares to the actual Neumann inverse.  In
particular the inverse square root in this file is constructed, not supplied
as an additional input.  The convolution is the Chu--Vandermonde identity.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar
open scoped Topology

theorem minus_half_choose_convolution (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n,
      Ring.choose (-1 / 2 : ℝ) ij.1 * Ring.choose (-1 / 2 : ℝ) ij.2 = (-1 : ℝ) ^ n := by
  rw [← Ring.add_choose_eq n (Commute.refl (-1 / 2 : ℝ))]
  norm_num only [show (-1 / 2 : ℝ) + (-1 / 2 : ℝ) = -1 by norm_num]
  rw [Ring.choose_neg', Ring.multichoose_one]
  simp [Units.smul_def]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem actualInvSqrt_mul_self (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    actualInvSqrt E * actualInvSqrt E = ∑' n : ℕ, E ^ n := by
  rw [actualInvSqrt_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_actualInvSqrt E hE) (summable_norm_actualInvSqrt E hE)]
  apply tsum_congr
  intro n
  calc
    _ = (∑ ij ∈ Finset.antidiagonal n,
        Ring.choose (-1 / 2 : ℝ) ij.1 * Ring.choose (-1 / 2 : ℝ) ij.2) • (-E) ^ n := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [smul_mul_smul_comm, ← pow_add, Finset.mem_antidiagonal.mp hij]
    _ = (-1 : ℝ) ^ n • (-E) ^ n := by rw [minus_half_choose_convolution]
    _ = E ^ n := by
      rw [← neg_one_smul ℝ E, smul_pow, smul_smul, ← mul_pow]
      norm_num

theorem actualInvSqrt_mul_self_one_sub (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    actualInvSqrt E * actualInvSqrt E * (1 - E) = 1 := by
  rw [actualInvSqrt_mul_self E hE]
  exact geom_series_mul_neg E hE

theorem one_sub_actualInvSqrt_mul_self (E : V →L[ℝ] V) (hE : ‖E‖ < 1) :
    (1 - E) * (actualInvSqrt E * actualInvSqrt E) = 1 := by
  rw [actualInvSqrt_mul_self E hE]
  exact (summable_geometric_of_norm_lt_one hE).one_sub_mul_tsum_pow

omit [CompleteSpace V] in
theorem actualInvSqrt_commute (E A : V →L[ℝ] V) (h : Commute E A) :
    Commute (actualInvSqrt E) A := by
  rw [actualInvSqrt_eq_tsum]
  apply Commute.tsum_left
  intro n
  exact ((h.neg_left).pow_left n).smul_left _

theorem actualInvSqrt_selfAdjoint (E : V →L[ℝ] V) (hE : IsSelfAdjoint E) :
    IsSelfAdjoint (actualInvSqrt E) := by
  rw [actualInvSqrt_eq_tsum]
  change star (∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • (-E) ^ n) = _
  rw [tsum_star]
  apply tsum_congr
  intro n
  simp only [star_smul, star_pow, star_neg, hE.star_eq, star_trivial]

end GlobalEmbedding.NormalPolar
