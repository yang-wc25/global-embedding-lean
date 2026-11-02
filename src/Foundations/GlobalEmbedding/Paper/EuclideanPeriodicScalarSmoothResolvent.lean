import GlobalEmbedding.Paper.BasisPeriodicSmoothResolvent
import GlobalEmbedding.Paper.EuclideanCoordinateLaplacian

open Module WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Genuine smooth scalar solvability for the original period-one coordinate operator.
The integer lattice of the actual Euclidean coordinate basis is identified in both
directions with the original integer-coordinate vectors. Apply the proved real-basis
periodic construction, then the actual coordinate Laplacian formula. Every a≥0,
including odd a and the empty coordinate sum, is covered. -/
theorem exists_euclidean_periodic_scalar_smooth_resolvent
    {a : ℕ} (f : EuclideanSpace ℝ (Fin a) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ x (m : Fin a → ℤ),
      f (x + toLp 2 (fun i => (m i : ℝ))) = f x) :
    ∃ u : EuclideanSpace ℝ (Fin a) → ℝ, ContDiff ℝ ∞ u ∧
      (∀ x (m : Fin a → ℤ), u (x + toLp 2 (fun i => (m i : ℝ))) = u x) ∧
      ∀ x, (∑ i : Fin a, fderiv ℝ
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin a) ℝ i)) x
        (EuclideanSpace.basisFun (Fin a) ℝ i)) - u x = f x := by
  classical
  let b := (EuclideanSpace.basisFun (Fin a) ℝ).toBasis
  let L := Submodule.span ℤ (Set.range b)
  have hcoords (z : L) (i : Fin a) : ∃ m : ℤ, (m : ℝ) = (z : EuclideanSpace ℝ (Fin a)) i := by
    have H := (b.mem_span_iff_repr_mem ℤ (z : EuclideanSpace ℝ (Fin a))).mp z.property i
    simpa [b] using H
  have hp (z : L) (x : EuclideanSpace ℝ (Fin a)) : f (x + z) = f x := by
    choose m hm using hcoords z
    have he : toLp 2 (fun i => (m i : ℝ)) = (z : EuclideanSpace ℝ (Fin a)) := by
      ext i
      exact hm i
    rw [← he]
    exact hperiod x m
  obtain ⟨u, hu, hup, he⟩ := exists_smooth_basis_periodic_resolvent b f hf hp
  refine ⟨u, hu, ?_, fun x => ?_⟩
  · intro x m
    have hm : toLp 2 (fun i => (m i : ℝ)) ∈ L := by
      apply (b.mem_span_iff_repr_mem ℤ _).mpr
      intro i
      exact ⟨m i, by simp [b]⟩
    exact hup ⟨_, hm⟩ x
  · rw [← euclidean_laplacian_eq_coordinate_second u (hu.of_le (by simp)) x]
    exact he x

#print axioms exists_euclidean_periodic_scalar_smooth_resolvent

end GlobalEmbedding.Paper
