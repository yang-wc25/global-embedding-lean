import Probes.ActualIncrementChosenMarginReserve

/-!
# Actual zero-first-coordinate charts on the chosen phase kernel

The kernel equivalence is constructed from the genuine inverse-chart linear
equivalence. Its inverse is exactly the tail of the forward derivative,
whose native Euclidean operator norm is at most one. Thus a forward-chart
norm budget supplies the inverse bound required by the chosen-margin reserve.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Bundle
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

def actualIncrementZeroInsert (m : ℕ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) :=
  (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Fin.cases 0 (fun a => EuclideanSpace.proj a) i)

def actualIncrementTail (m : ℕ) :
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a => EuclideanSpace.proj a.succ)

@[simp] theorem actualIncrementZeroInsert_zero (m : ℕ)
    (v : EuclideanSpace ℝ (Fin m)) : actualIncrementZeroInsert m v 0 = 0 := rfl

@[simp] theorem actualIncrementZeroInsert_succ (m : ℕ)
    (v : EuclideanSpace ℝ (Fin m)) (a : Fin m) :
    actualIncrementZeroInsert m v a.succ = v a := rfl

@[simp] theorem actualIncrementTail_apply (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (m+1))) (a : Fin m) :
    actualIncrementTail m v a = v a.succ := rfl

@[simp] theorem actualIncrementTail_zeroInsert (m : ℕ)
    (v : EuclideanSpace ℝ (Fin m)) :
    actualIncrementTail m (actualIncrementZeroInsert m v) = v := by
  ext a
  rfl

theorem actualIncrementZeroInsert_tail (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (m+1))) (hv : v 0 = 0) :
    actualIncrementZeroInsert m (actualIncrementTail m v) = v := by
  ext a
  refine Fin.cases ?_ (fun b => ?_) a
  · exact hv.symm
  · rfl

theorem actualIncrementZeroInsert_single (m : ℕ) (a : Fin m) :
    actualIncrementZeroInsert m (EuclideanSpace.single a 1) =
      EuclideanSpace.single a.succ 1 := by
  ext b
  refine Fin.cases ?_ (fun k => ?_) b
  · simp
  · simp

theorem actualIncrementTail_norm (m : ℕ) (v : EuclideanSpace ℝ (Fin (m+1))) :
    ‖actualIncrementTail m v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [actualIncrementTail_apply]
  exact le_add_of_nonneg_left (sq_nonneg (v 0))

theorem actualIncrementTail_norm_le (m : ℕ) : ‖actualIncrementTail m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using actualIncrementTail_norm m v

section Kernel
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)

def actualIncrementCoordinateCovector (A : D ≃L[ℝ] E) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0).comp A.symm.toContinuousLinearMap

def actualIncrementCoordinateKernelMap (A : D ≃L[ℝ] E) :
    D0 →L[ℝ] (actualIncrementCoordinateCovector A).ker :=
  (A.toContinuousLinearMap.comp (actualIncrementZeroInsert m)).codRestrict
    (actualIncrementCoordinateCovector A).ker (by
      intro v
      change (A.symm (A (actualIncrementZeroInsert m v))) 0 = 0
      rw [A.symm_apply_apply]
      rfl)

def actualIncrementCoordinateKernelInverse (A : D ≃L[ℝ] E) :
    (actualIncrementCoordinateCovector A).ker →L[ℝ] D0 :=
  (actualIncrementTail m).comp (A.symm.toContinuousLinearMap.comp
    (actualIncrementCoordinateCovector A).ker.subtypeL)

def actualIncrementCoordinateKernelEquiv (A : D ≃L[ℝ] E) :
    D0 ≃L[ℝ] (actualIncrementCoordinateCovector A).ker :=
  ContinuousLinearEquiv.equivOfInverse
    (actualIncrementCoordinateKernelMap A) (actualIncrementCoordinateKernelInverse A)
    (by
      intro v
      change actualIncrementTail m (A.symm (A (actualIncrementZeroInsert m v))) = v
      simp)
    (by
      intro w
      apply Subtype.ext
      change A (actualIncrementZeroInsert m (actualIncrementTail m (A.symm w))) = w
      rw [actualIncrementZeroInsert_tail m (A.symm w) (by exact w.property)]
      exact A.apply_symm_apply w)

theorem actualIncrementCoordinateKernelEquiv_single (A : D ≃L[ℝ] E) (a : Fin m) :
    ((actualIncrementCoordinateKernelEquiv A (EuclideanSpace.single a 1)) : E) =
      A (EuclideanSpace.single a.succ 1) := by
  change A (actualIncrementZeroInsert m (EuclideanSpace.single a 1)) = _
  rw [actualIncrementZeroInsert_single]

/-- The actual kernel-coordinate inverse is bounded by the genuine forward
chart derivative, without a further dimension or norm-conversion loss. -/
theorem actualIncrementCoordinateKernelEquiv_inverse_norm (A : D ≃L[ℝ] E) :
    ‖(actualIncrementCoordinateKernelEquiv A).symm.toContinuousLinearMap‖ ≤
      ‖A.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  change ‖actualIncrementTail m (A.symm w)‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖w‖
  exact (actualIncrementTail_norm m (A.symm w)).trans (A.symm.toContinuousLinearMap.le_opNorm w)

end Kernel
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualIncrementCoordinateKernelEquiv
#print axioms GlobalEmbedding.Continuation.actualIncrementCoordinateKernelEquiv_inverse_norm
