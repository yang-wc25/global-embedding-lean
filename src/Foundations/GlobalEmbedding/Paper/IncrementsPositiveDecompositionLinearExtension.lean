import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# The original positive decomposition extends as a linear identity

Source: main.tex595–598,638–672. On the SAME symmetric tensor fiber, replace
(chi * sqrt (L A))² by chi² * L A on the original positive neighborhood.
The resulting reconstruction is linear. Its difference from identity has a
kernel containing a nonempty open set, so the native submodule interior lemma
makes that kernel the whole fiber. No new tensor carrier, norm, or decomposition
is introduced. Positivity remains required for the actual square-root formula;
no membership of finite iterates in an arbitrary original neighborhood follows.
DAG: increments-positive-decomposition-linear-extension. Exclusive worker W3.
-/

noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.Paper

/-- The given ORIGINAL positive square-root decomposition implies its linear
identity on the entire SAME real tensor fiber. The cutoff-zero case needs no
square-root positivity. This is the domain-extension step used by the positive
reserve checks in main.tex659–662; it supplies no new quantitative assumption. -/
theorem increments_positive_decomposition_linear_extension
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {ι : Type*} [Fintype ι] (L : ι → E →ₗ[ℝ] ℝ) (chi : ι → ℝ) (Q : ι → E)
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (hpos : ∀ A ∈ U, ∀ ν, chi ν ≠ 0 → 0 ≤ L ν A)
    (hdecomp : ∀ A ∈ U, A = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν) :
    ∀ A : E, A = ∑ ν, (chi ν ^ 2 * L ν A) • Q ν := by
  let R : E →ₗ[ℝ] E := ∑ ν, (chi ν ^ 2) • (L ν).smulRight (Q ν)
  have hR (A : E) : R A = ∑ ν, (chi ν ^ 2 * L ν A) • Q ν := by
    simp [R, smul_smul]
  have hlocal : U ⊆ (LinearMap.ker (LinearMap.id - R) : Set E) := by
    intro A hA
    have heq : A = R A := by
      calc
        A = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν := hdecomp A hA
        _ = R A := by
          rw [hR]
          apply Finset.sum_congr rfl
          intro ν _
          by_cases hc : chi ν = 0
          · simp [hc]
          · rw [mul_pow, Real.sq_sqrt (hpos A hA ν hc)]
    change A - R A = 0
    exact sub_eq_zero.mpr heq
  have hker : LinearMap.ker (LinearMap.id - R) = ⊤ :=
    (LinearMap.ker (LinearMap.id - R)).eq_top_of_nonempty_interior'
      (hne.mono (interior_maximal hlocal hU))
  intro A
  have hA : A ∈ LinearMap.ker (LinearMap.id - R) := by rw [hker]; trivial
  have heq : A = R A := by
    change A - R A = 0 at hA
    exact sub_eq_zero.mp hA
  exact heq.trans (hR A)

/-- The SAME square-root formula is valid at every tensor whose arguments are
positive where its cutoff is nonzero. Reuse the original open-neighborhood
linear extension; no intermediate membership in that arbitrary neighborhood
is required. This is exactly the positive-reserve domain used in main.tex659–662.
It does NOT prove that any computed iterate satisfies those reserve checks. -/
theorem increments_positive_decomposition_on_reserve
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {ι : Type*} [Fintype ι] (L : ι → E →ₗ[ℝ] ℝ) (chi : ι → ℝ) (Q : ι → E)
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (hpos : ∀ A ∈ U, ∀ ν, chi ν ≠ 0 → 0 ≤ L ν A)
    (hdecomp : ∀ A ∈ U, A = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν)
    (A : E) (hA : ∀ ν, chi ν ≠ 0 → 0 ≤ L ν A) :
    A = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν := by
  calc
    A = ∑ ν, (chi ν ^ 2 * L ν A) • Q ν :=
      increments_positive_decomposition_linear_extension L chi Q U hU hne hpos hdecomp A
    _ = ∑ ν, (chi ν * Real.sqrt (L ν A)) ^ 2 • Q ν := by
      apply Finset.sum_congr rfl
      intro ν _
      by_cases hc : chi ν = 0
      · simp [hc]
      · rw [mul_pow, Real.sq_sqrt (hA ν hc)]

end GlobalEmbedding.Paper
