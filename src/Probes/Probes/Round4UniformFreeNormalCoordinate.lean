import Probes.ActualFreeNormalProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Uniform ambient-coordinate selection for the actual free-normal projection.
The dimension condition produces a unit fixed vector of the two projections.
An ambient coordinate then has projection at least 1/(N+1). This deliberately
conservative positive reserve depends only on N, not on the map or number of
charts. The resulting normalized vector belongs to the two actual kernels.
-/

noncomputable section
open Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation

variable {N : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin N)

def round4AmbientCoordinateReserve (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

theorem round4AmbientCoordinateReserve_pos (N : ℕ) :
    0 < round4AmbientCoordinateReserve N := by
  unfold round4AmbientCoordinateReserve
  positivity

/-- A unit fixed vector forces one actual coordinate column to be uniformly
nonzero. This estimate uses the original Euclidean coordinate vectors. -/
theorem round4_coordinate_reserve_of_unit_fixed_vector
    (P : V →L[ℝ] V) (v : V) (hv : ‖v‖ = 1) (hPv : P v = v) :
    ∃ i : Fin N, round4AmbientCoordinateReserve N ≤ ‖P (EuclideanSpace.single i 1)‖ := by
  classical
  by_contra h
  push Not at h
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  have hsum : ∑ i : Fin N, v i • EuclideanSpace.single i 1 = v := by
    simpa only [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using e.sum_repr v
  have htotal : 1 ≤ (N : ℝ) * round4AmbientCoordinateReserve N := by
    calc
      1 = ‖P v‖ := by rw [hPv, hv]
      _ = ‖∑ i : Fin N, P (v i • EuclideanSpace.single i 1)‖ := by rw [← map_sum, hsum]
      _ ≤ ∑ i : Fin N, ‖P (v i • EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, round4AmbientCoordinateReserve N := by
        apply Finset.sum_le_sum
        intro i _
        rw [map_smul, norm_smul]
        have hvi : ‖v i‖ ≤ 1 := (PiLp.norm_apply_le v i).trans_eq hv
        exact (mul_le_mul hvi (h i).le (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = (N : ℝ) * round4AmbientCoordinateReserve N := by simp
  have hless : (N : ℝ) * round4AmbientCoordinateReserve N < 1 := by
    unfold round4AmbientCoordinateReserve
    rw [mul_one_div]
    exact (div_lt_one (by positivity : 0 < (N : ℝ)+1)).mpr (by linarith)
  exact (not_le_of_gt hless) htotal

variable {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

/-- The actual rank deficit produces the coordinate reserve; the reserve is
not a hypothesis. The two frames need not first be replaced by chosen bases. -/
theorem round4_actual_free_normal_coordinate_reserve
    (A : E →L[ℝ] V) (B : T →L[ℝ] V)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ T < N) :
    ∃ i : Fin N,
      round4AmbientCoordinateReserve N ≤
        ‖actualFreeNormalProjectionRaw A B (EuclideanSpace.single i 1)‖ := by
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  have hSdim : Module.finrank ℝ S ≤ Module.finrank ℝ E + Module.finrank ℝ T :=
    (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add (LinearMap.finrank_range_le A.toLinearMap)
        (LinearMap.finrank_range_le B.toLinearMap))
  have hS : S ≠ ⊤ := by
    intro htop
    have hh := hSdim
    rw [htop] at hh
    have hh' : N ≤ Module.finrank ℝ E + Module.finrank ℝ T := by
      simpa only [finrank_top, finrank_euclideanSpace, Fintype.card_fin] using hh
    omega
  have hK : Sᗮ ≠ ⊥ := fun h => hS (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let u := NormedSpace.normalize v
  have huK : u ∈ Sᗮ := Sᗮ.smul_mem _ hvK
  have huA : u ∈ (LinearMap.range A.toLinearMap)ᗮ :=
    (Submodule.orthogonal_le (show LinearMap.range A.toLinearMap ≤ S from le_sup_left)) huK
  have huB : u ∈ (LinearMap.range B.toLinearMap)ᗮ :=
    (Submodule.orthogonal_le (show LinearMap.range B.toLinearMap ≤ S from le_sup_right)) huK
  let P := (LinearMap.range B.toLinearMap)ᗮ.starProjection.comp
    (LinearMap.range A.toLinearMap)ᗮ.starProjection
  have hPu : P u = u := by
    change (LinearMap.range B.toLinearMap)ᗮ.starProjection
      ((LinearMap.range A.toLinearMap)ᗮ.starProjection u) = u
    rw [Submodule.starProjection_eq_self_iff.mpr huA,
      Submodule.starProjection_eq_self_iff.mpr huB]
  exact round4_coordinate_reserve_of_unit_fixed_vector P u
    (NormedSpace.norm_normalize hv0) hPu

theorem round4_actual_unit_free_normal_from_coordinate
    (A : E →L[ℝ] V) (B : T →L[ℝ] V)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ T < N)
    (hRange : LinearMap.range B.toLinearMap ≤ (LinearMap.range A.toLinearMap)ᗮ) :
    ∃ i : Fin N,
      round4AmbientCoordinateReserve N ≤
        ‖actualFreeNormalProjectionRaw A B (EuclideanSpace.single i 1)‖ ∧
      let normal := NormedSpace.normalize
        (actualFreeNormalProjectionRaw A B (EuclideanSpace.single i 1))
      ‖normal‖ = 1 ∧ normal ∈ (LinearMap.range A.toLinearMap)ᗮ ∧
        normal ∈ (LinearMap.range B.toLinearMap)ᗮ := by
  obtain ⟨i, hi⟩ := round4_actual_free_normal_coordinate_reserve A B hdim
  have hpos := (round4AmbientCoordinateReserve_pos N).trans_le hi
  have hmem := actual_free_normal_projection_mem A B (EuclideanSpace.single i 1) hRange
  exact ⟨i, hi, NormedSpace.norm_normalize (norm_pos_iff.mp hpos),
    (LinearMap.range A.toLinearMap)ᗮ.smul_mem _ hmem.1,
    (LinearMap.range B.toLinearMap)ᗮ.smul_mem _ hmem.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_free_normal_coordinate_reserve
#print axioms GlobalEmbedding.Continuation.round4_actual_unit_free_normal_from_coordinate
