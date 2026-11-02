import GlobalEmbedding.Paper.EuclideanPeriodicScalarSmoothResolvent
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open WithLp
open scoped ContDiff Laplacian

namespace GlobalEmbedding.Paper

/-- Genuine smooth solvability of the original period-one shifted coordinate Laplacian
for every finite Euclidean target. Solve each actual scalar coordinate, assemble by
the true Euclidean toLp map, and commute the actual Laplacian with genuine bounded
linear coordinate projections. Both source and target dimensions may be zero. -/
theorem exists_euclidean_periodic_smooth_resolvent
    {a N : ℕ} (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ x (m : Fin a → ℤ),
      f (x + toLp 2 (fun i => (m i : ℝ))) = f x) :
    ∃ u : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ u ∧
      (∀ x (m : Fin a → ℤ), u (x + toLp 2 (fun i => (m i : ℝ))) = u x) ∧
      ∀ x, (∑ i : Fin a, fderiv ℝ
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin a) ℝ i)) x
        (EuclideanSpace.basisFun (Fin a) ℝ i)) - u x = f x := by
  have hfi (j : Fin N) : ContDiff ℝ ∞ (fun x => f x j) := (contDiff_piLp 2).mp hf j
  have hpi (j : Fin N) (x) (m : Fin a → ℤ) :
      f (x + toLp 2 (fun i => (m i : ℝ))) j = f x j := congrArg (fun y => y j) (hperiod x m)
  choose v hv hp he using fun j =>
    exists_euclidean_periodic_scalar_smooth_resolvent (fun x => f x j) (hfi j) (hpi j)
  let u : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N) :=
    fun x => toLp 2 (fun j => v j x)
  have hu : ContDiff ℝ ∞ u := (contDiff_piLp 2).mpr hv
  refine ⟨u, hu, ?_, fun x => ?_⟩
  · intro x m
    ext j
    exact hp j x m
  · rw [← euclidean_laplacian_eq_coordinate_second u (hu.of_le (by simp)) x]
    ext j
    have hcomm : Laplacian.laplacian (v j) x = (Laplacian.laplacian u x) j := by
      simpa only [u, Function.comp_def, PiLp.proj_apply] using
        (hu.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).contDiffAt.laplacian_CLM_comp_left
          (l := PiLp.proj 2 (fun _ : Fin N => ℝ) j)
    change (Laplacian.laplacian u x) j - v j x = f x j
    rw [← hcomm, euclidean_laplacian_eq_coordinate_second (v j) ((hv j).of_le (by simp)) x]
    exact he j x

#print axioms exists_euclidean_periodic_smooth_resolvent

end GlobalEmbedding.Paper
