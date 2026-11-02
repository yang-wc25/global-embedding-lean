import Probes.ActualIncrementKernelCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Native Euclidean splitting and a quantitatively normalized phase direction

The Euclidean model is never identified isometrically with a max-norm product.
The genuine split has norm at most one, its inverse at most two. A real orthogonal
reflection sends the first Euclidean basis vector to a norm-attaining direction
of the original spatial phase differential.
-/

noncomputable section
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def actualEuclideanPhaseSplit (m : ℕ) :
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) :=
  (EuclideanSpace.proj 0).prod (actualIncrementTail m)

def actualEuclideanPhaseJoin (m : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 1)).comp
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))) +
    (actualIncrementZeroInsert m).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))

theorem actualIncrementZeroInsert_norm (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    ‖actualIncrementZeroInsert m v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  simp

@[simp] theorem actualEuclideanPhaseJoin_zero (m : ℕ)
    (z : ℝ × EuclideanSpace ℝ (Fin m)) : actualEuclideanPhaseJoin m z 0 = z.1 := by
  simp [actualEuclideanPhaseJoin]

@[simp] theorem actualEuclideanPhaseJoin_succ (m : ℕ)
    (z : ℝ × EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    actualEuclideanPhaseJoin m z i.succ = z.2 i := by
  simp [actualEuclideanPhaseJoin]

def actualEuclideanPhaseEquiv (m : ℕ) :
    EuclideanSpace ℝ (Fin (m+1)) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) :=
  ContinuousLinearEquiv.equivOfInverse (actualEuclideanPhaseSplit m) (actualEuclideanPhaseJoin m)
    (by
      intro x
      ext i
      refine Fin.cases ?_ (fun a => ?_) i
      · exact actualEuclideanPhaseJoin_zero m _
      · exact actualEuclideanPhaseJoin_succ m _ a)
    (by
      intro z
      refine Prod.ext ?_ ?_
      · exact actualEuclideanPhaseJoin_zero m z
      · ext i
        exact actualEuclideanPhaseJoin_succ m z i)

@[simp] theorem actualEuclideanPhaseEquiv_fst (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    (actualEuclideanPhaseEquiv m x).1 = x 0 := rfl

@[simp] theorem actualEuclideanPhaseEquiv_snd (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    (actualEuclideanPhaseEquiv m x).2 = actualIncrementTail m x := rfl

@[simp] theorem actualEuclideanPhaseEquiv_symm_zero (m : ℕ)
    (z : ℝ × EuclideanSpace ℝ (Fin m)) :
    (actualEuclideanPhaseEquiv m).symm z 0 = z.1 := actualEuclideanPhaseJoin_zero m z

@[simp] theorem actualEuclideanPhaseEquiv_symm_axis (m : ℕ) :
    (actualEuclideanPhaseEquiv m).symm (1,0) = EuclideanSpace.single 0 1 := by
  change actualEuclideanPhaseJoin m (1,0) = _
  simp [actualEuclideanPhaseJoin]

theorem actualEuclideanPhaseEquiv_norm (m : ℕ) :
    ‖(actualEuclideanPhaseEquiv m : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin m)))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x 0,actualIncrementTail m x)‖ ≤ 1*‖x‖
  rw [one_mul,Prod.norm_def]
  exact max_le (PiLp.norm_apply_le x 0) (actualIncrementTail_norm m x)

theorem actualEuclideanPhaseEquiv_symm_norm (m : ℕ) :
    ‖((actualEuclideanPhaseEquiv m).symm : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖z.1 • EuclideanSpace.single 0 (1:ℝ)+actualIncrementZeroInsert m z.2‖ ≤ 2*‖z‖
  calc
    _ ≤ ‖z.1 • EuclideanSpace.single 0 (1:ℝ)‖+‖actualIncrementZeroInsert m z.2‖ := norm_add_le _ _
    _ = ‖z.1‖+‖z.2‖ := by rw [norm_smul,actualIncrementZeroInsert_norm]; simp
    _ ≤ 2*‖z‖ := by linarith [norm_fst_le z,norm_snd_le z]

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]

theorem actual_phase_covector_unit_direction (d : D →L[ℝ] ℝ) (hd : d ≠ 0) :
    ∃ v : D, ‖v‖ = 1 ∧ d v = ‖d‖ := by
  let u := (InnerProductSpace.toDual ℝ D).symm d
  have hun : ‖u‖ = ‖d‖ := (InnerProductSpace.toDual ℝ D).symm.norm_map d
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  refine ⟨‖d‖⁻¹ • u,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hdpos),hun,inv_mul_cancel₀ hdpos.ne']
  · rw [map_smul]
    have hu : d u = ‖d‖^2 := by
      rw [← InnerProductSpace.toDual_symm_apply]
      change inner ℝ u u = _
      rw [real_inner_self_eq_norm_sq,hun]
    change ‖d‖⁻¹ * d u = _
    rw [hu]
    field_simp

/-- Orthogonal orientation is chosen from the actual noncritical covector.
No chosen-coordinate lower bound or unbounded basis conversion is assumed. -/
theorem actual_exists_phase_orientation (m : ℕ)
    (d : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ) (hd : d ≠ 0) :
    ∃ R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)),
      d (R (EuclideanSpace.single 0 1)) = ‖d‖ := by
  obtain ⟨v,hv,hdv⟩ := actual_phase_covector_unit_direction d hd
  let R := (ℝ ∙ (EuclideanSpace.single 0 1-v))ᗮ.reflection
  refine ⟨R,?_⟩
  have he : R (EuclideanSpace.single 0 1) = v :=
    Submodule.reflection_sub (by simpa using hv.symm)
  rw [he]
  exact hdv

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualEuclideanPhaseEquiv_norm
#print axioms GlobalEmbedding.Continuation.actualEuclideanPhaseEquiv_symm_norm
#print axioms GlobalEmbedding.Continuation.actual_exists_phase_orientation
