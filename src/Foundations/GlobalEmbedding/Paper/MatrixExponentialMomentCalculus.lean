import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Ring

/-!
# Actual finite exponential moment calculus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines345–350.
The potential, gradient and Hessian are actual finite formulas; none is supplied as a solver.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal finite exponential potential for the prescribed moment. -/
def matrixExponentialPotential (v : ι → E) (y x : E) : ℝ :=
  ∑ i, Real.exp ⟪v i, x⟫ - ⟪y, x⟫

/-- The actual gradient before subtracting the prescribed moment. -/
def matrixExponentialMoment (v : ι → E) (x : E) : E :=
  ∑ i, Real.exp ⟪v i, x⟫ • v i

/-- The actual positive weighted rank-one Hessian of the finite potential. -/
def matrixExponentialHessian (v : ι → E) (x : E) : E →L[ℝ] E :=
  ∑ i, Real.exp ⟪v i, x⟫ • InnerProductSpace.rankOne ℝ (v i) (v i)

/-- Differentiating the literal moment map gives its actual rank-one Hessian. -/
theorem matrixExponentialMoment_hasFDerivAt (v : ι → E) (x : E) :
    HasFDerivAt (matrixExponentialMoment v) (matrixExponentialHessian v x) x := by
  have hi (i : ι) : HasFDerivAt (fun z : E ↦ Real.exp ⟪v i, z⟫ • v i)
      (Real.exp ⟪v i, x⟫ • InnerProductSpace.rankOne ℝ (v i) (v i)) x := by
    have hh := ((innerSL ℝ (v i)).hasFDerivAt (x := x)).exp.smul_const (v i)
    have he : Real.exp ⟪v i, x⟫ • InnerProductSpace.rankOne ℝ (v i) (v i) =
        (Real.exp ⟪v i, x⟫ • innerSL ℝ (v i)).smulRight (v i) := by
      apply ContinuousLinearMap.ext
      intro u
      simp [smul_smul]
    rw [he]
    exact hh
  exact HasFDerivAt.fun_sum (fun i _ ↦ hi i)

/-- The derivative of the literal potential is precisely the prescribed-moment defect. -/
theorem matrixExponentialPotential_hasFDerivAt (v : ι → E) (y x : E) :
    HasFDerivAt (matrixExponentialPotential v y)
      (innerSL ℝ (matrixExponentialMoment v x - y)) x := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ ((innerSL ℝ (v i)).hasFDerivAt (x := x)).exp)).sub
      ((innerSL ℝ y).hasFDerivAt (x := x))
  convert hd using 1
  · rfl
  · ext u
    simp [matrixExponentialMoment, sum_apply]

/-- The actual Hessian quadratic form is the positive weighted sum of real squares. -/
theorem matrixExponentialHessian_quadratic (v : ι → E) (x u : E) :
    ⟪u, matrixExponentialHessian v x u⟫ =
      ∑ i, Real.exp ⟪v i, x⟫ * ⟪v i, u⟫ ^ 2 := by
  simp [matrixExponentialHessian, inner_sum, real_inner_smul_right,
    real_inner_comm, pow_two]

/-- Genuine directionwise positive spanning forces the actual Hessian to be positive definite.
In zero dimension the assertion is vacuous; no unwanted nonzero-dimension hypothesis is added. -/
theorem matrixExponentialHessian_pos (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (x u : E) (hu : u ≠ 0) :
    0 < ⟪u, matrixExponentialHessian v x u⟫ := by
  rw [matrixExponentialHessian_quadratic]
  obtain ⟨i, hi⟩ := hspan u hu
  apply Finset.sum_pos' (fun j _ ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  exact ⟨i, Finset.mem_univ _, mul_pos (Real.exp_pos _) (sq_pos_of_pos hi)⟩

/-- The actual moment map is strictly monotone in the inner-product sense. -/
theorem matrixExponentialMoment_strict (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫)
    (x z : E) (hxz : x ≠ z) :
    0 < ⟪matrixExponentialMoment v x - matrixExponentialMoment v z, x - z⟫ := by
  have he : ⟪matrixExponentialMoment v x - matrixExponentialMoment v z, x - z⟫ =
      ∑ i, (Real.exp ⟪v i, x⟫ - Real.exp ⟪v i, z⟫) *
        (⟪v i, x⟫ - ⟪v i, z⟫) := by
    unfold matrixExponentialMoment
    rw [← Finset.sum_sub_distrib, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right]
    ring
  rw [he]
  have hn (i : ι) : 0 ≤ (Real.exp ⟪v i, x⟫ - Real.exp ⟪v i, z⟫) *
      (⟪v i, x⟫ - ⟪v i, z⟫) := by
    by_cases hle : ⟪v i, x⟫ ≤ ⟪v i, z⟫
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.exp_le_exp.mpr hle)) (sub_nonpos.mpr hle)
    · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (le_of_not_ge hle)))
        (sub_nonneg.mpr (le_of_not_ge hle))
  obtain ⟨i, hi⟩ := hspan (x - z) (sub_ne_zero.mpr hxz)
  rw [inner_sub_right] at hi
  refine Finset.sum_pos' (fun j _ ↦ hn j) ⟨i, Finset.mem_univ _, ?_⟩
  exact mul_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (sub_pos.mp hi))) hi

/-- Genuine positive spanning gives uniqueness of every prescribed exponential moment. -/
theorem matrixExponentialMoment_injective (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) :
    Function.Injective (matrixExponentialMoment v) := by
  intro x z he
  by_contra hn
  have hp := matrixExponentialMoment_strict v hspan x z hn
  rw [he, sub_self, inner_zero_left] at hp
  exact lt_irrefl _ hp

#print axioms matrixExponentialMoment_injective
#print axioms matrixExponentialMoment_hasFDerivAt
#print axioms matrixExponentialPotential_hasFDerivAt
#print axioms matrixExponentialHessian_pos

end GlobalEmbedding.Paper
