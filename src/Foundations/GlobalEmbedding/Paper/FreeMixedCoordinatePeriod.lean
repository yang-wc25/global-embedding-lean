import GlobalEmbedding.Paper.MatrixOrbitCalculus
import GlobalEmbedding.Paper.PlanarHopfFlow
import GlobalEmbedding.Paper.FreeDisplacementCoordinates
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Actual mixed-period cancellation for the free-induction displacement

Source: `main.tex`, `thm:free`, lines441–453.
DAG: `free-mixed-coordinate-period`; exclusive owner W2.
The four original terms are controlled by the actual matrix periods,
actual periodic integration by parts, and genuine unit-normal identities.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise RealInnerProductSpace
open MeasureTheory

namespace GlobalEmbedding.Paper

variable {C d : ℕ}

local instance freeMixedPeriodMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

private theorem matrix_action_inner_mul
    (M N : Matrix (Fin d) (Fin d) ℝ) (a b : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) M a, Matrix.toEuclideanCLM (𝕜 := ℝ) N b⟫ =
      ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (M.transpose * N) b⟫ := by
  rw [← (Matrix.toEuclideanCLM (𝕜 := ℝ) M).adjoint_inner_right]
  change ⟪a, (star (Matrix.toEuclideanCLM (𝕜 := ℝ) M) *
    Matrix.toEuclideanCLM (𝕜 := ℝ) N) b⟫ = _
  rw [← map_star, ← map_mul]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Orthogonal matrices preserve actual Euclidean inner products. Source: the orthogonal
coordinate calculation in main.tex441–453; reusable in the active pivot at461–470. -/
theorem matrix_action_inner_orthogonal
    (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (a b : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Q a, Matrix.toEuclideanCLM (𝕜 := ℝ) Q b⟫ = ⟪a, b⟫ := by
  rw [matrix_action_inner_mul,
    ((Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp hQ).1)]
  simp only [map_one, one_apply_eq_self]

private def matrixBilinearCLM (a b : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
  (innerSL ℝ a).comp ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d)) b).comp
    (((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) :
      Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))).toContinuousLinearEquiv.toContinuousLinearMap))

private theorem matrix_average_bilinear
    (M : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ) (z : PlanarHopfSphere C)
    (hM : Continuous (fun t : ℝ ↦ M (planarHopfFlow t z)))
    (a b : EuclideanSpace ℝ (Fin d)) :
    orbitAverage planarHopfFlow
      (fun w ↦ ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (M w) b⟫) z =
        ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitAverage planarHopfFlow M z) b⟫ := by
  exact (matrixBilinearCLM a b).intervalIntegral_comp_comm
    (hM.intervalIntegrable (μ := volume) 0 1)

variable [Fact (0 < C)]

/-- The base-base term has zero actual period by the literal matrix P-transpose-Q period. -/
theorem free_mixed_base_period_zero
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (da a : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (fun w ↦
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫) z = 0 := by
  have hM : Continuous (fun w ↦ (P w).transpose * Q w) :=
    hP.continuous.matrix_transpose.mul hQ.continuous
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have he : (fun w ↦ ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫) =
      (fun w ↦ ⟪da, Matrix.toEuclideanCLM (𝕜 := ℝ) ((P w).transpose * Q w) a⟫) :=
    funext fun w ↦ matrix_action_inner_mul (P w) (Q w) da a
  rw [he, matrix_average_bilinear _ z (hM.comp hR) da a, hperiod z]
  simp only [map_zero, zero_apply, inner_zero_right]

/-- The remaining C-C term has zero actual period by the literal eta-squared matrix moment. -/
theorem free_mixed_quadratic_period_zero
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (dn n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (fun w ↦ η w ^ 2 *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫) z = 0 := by
  have hXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have hM : Continuous (fun w ↦ η w ^ 2 •
      ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) :=
    (hη.continuous.pow 2).smul (hQ.continuous.matrix_transpose.mul hXQ.continuous)
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have he : (fun w ↦ η w ^ 2 *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫) =
      (fun w ↦ ⟪dn, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) n⟫) := by
    funext w
    rw [matrix_action_inner_mul]
    simp only [map_smul, smul_apply, real_inner_smul_right]
  rw [he, matrix_average_bilinear _ z (hM.comp hR) dn n, hperiod z]
  simp only [map_zero, zero_apply, inner_zero_right]

/-- The first cross term has zero actual period by differentiating eta times
the actual P/Q pairing. The Q/Q contribution is zero by true orthogonality
of the old immersive column to the actual unit cofactor. -/
theorem free_mixed_first_cross_period_zero
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hPQ : ∀ w, orbitDeriv planarHopfFlow P w = Q w)
    (hSO : ∀ w, Q w ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (da n : EuclideanSpace ℝ (Fin d)) (horth : ⟪da, n⟫ = 0)
    (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (fun w ↦
      orbitDeriv planarHopfFlow η w *
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da, Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) n⟫ +
      η w * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫) z = 0 := by
  let φ : PlanarHopfSphere C → ℝ := fun w ↦ η w *
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da, Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) n⟫
  have hi : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun w ↦ ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) n⟫) :=
    (contDiff_inner : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) ↦ ⟪p.1, p.2⟫)).contMDiff.comp
        ((free_matrix_action_contMDiff P hP da).prodMk_space
          (free_matrix_action_contMDiff Q hQ n))
  have hφ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ φ := hη.mul hi
  have hd (w : PlanarHopfSphere C) : orbitDeriv planarHopfFlow φ w =
      orbitDeriv planarHopfFlow η w *
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da, Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) n⟫ +
      η w * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫ := by
    have hp := free_matrix_action_hasDerivAt P hP da w
    rw [hPQ w] at hp
    have hq := free_matrix_action_hasDerivAt Q hQ n w
    have he := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add η hη 0 w
    have h := he.fun_mul (hp.inner ℝ hq)
    simpa only [orbitDeriv, φ, planarHopfFlow_zero,
      matrix_action_inner_orthogonal (Q w) (hSO w), horth, zero_add, add_zero] using h.deriv
  have hzero := matrix_orbitDeriv_average_zero (planarHopfSmoothFlow C) φ hφ z
  change orbitAverage planarHopfFlow (orbitDeriv planarHopfFlow φ) z = 0 at hzero
  rw [funext hd] at hzero
  exact hzero

omit [Fact (0 < C)] in
/-- The second cross term is the true eta mean times the constant old-factor
pairing. This uses no unjustified pointwise cancellation of Yi n. -/
theorem free_mixed_second_cross_period_zero
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hSO : ∀ w, Q w ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (dn a : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (fun w ↦ η w *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫) z = 0 := by
  have he : (fun w ↦ η w *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫) =
      (fun w ↦ η w * ⟪dn, a⟫) := by
    funext w
    rw [matrix_action_inner_orthogonal (Q w) (hSO w)]
  rw [he]
  unfold orbitAverage
  rw [intervalIntegral.integral_mul_const]
  change orbitAverage planarHopfFlow η z * ⟪dn, a⟫ = 0
  rw [hmean z, zero_mul]

/-- All four original mixed coordinate periods cancel for the SAME actual
P,Q,eta. The eta Xeta term is retained and vanishes by <dn,n>=0.
This is the actual coordinate identity subsequently transported by the moving
complement frame, not an assumption that the desired mixed period is zero. -/
theorem free_mixed_coordinate_period_zero
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hPQ : ∀ w, orbitDeriv planarHopfFlow P w = Q w)
    (hSO : ∀ w, Q w ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (hperiod : ∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (hmean : ∀ z, orbitAverage planarHopfFlow η z = 0)
    (hquad : ∀ z, orbitAverage planarHopfFlow (fun w ↦
      η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0)
    (δ : ℝ) (a da n dn : EuclideanSpace ℝ (Fin d))
    (horth : ⟪da, n⟫ = 0) (hnormal : ⟪dn, n⟫ = 0) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (fun w ↦
      ⟪freeDisplacementOldVector P Q η δ da dn w,
        freeDisplacementActiveVector Q η δ a n w⟫) z = 0 := by
  let B := fun w ↦ ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
    Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫
  let L := fun w ↦ orbitDeriv planarHopfFlow η w *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da, Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) n⟫ +
    η w * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (P w) da,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫
  let R := fun w ↦ η w * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
    Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) a⟫
  let D := fun w ↦ η w ^ 2 * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q w) dn,
    Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q w) n⟫
  have hpda := (free_matrix_action_contMDiff P hP da).continuous
  have hqa := (free_matrix_action_contMDiff Q hQ a).continuous
  have hqn := (free_matrix_action_contMDiff Q hQ n).continuous
  have hqdn := (free_matrix_action_contMDiff Q hQ dn).continuous
  have hxqn := (free_matrix_action_contMDiff _
    (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ) n).continuous
  have hxe := (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) η hη).continuous
  have hB : Continuous B := hpda.inner hqa
  have hL : Continuous L :=
    (hxe.mul (hpda.inner hqn)).add (hη.continuous.mul (hpda.inner hxqn))
  have hR : Continuous R := hη.continuous.mul (hqdn.inner hqa)
  have hD : Continuous D := (hη.continuous.pow 2).mul (hqdn.inner hxqn)
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have iB : IntervalIntegrable (fun t ↦ B (planarHopfFlow t z)) volume 0 1 :=
    (hB.comp hflow).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have iL : IntervalIntegrable (fun t ↦ δ * L (planarHopfFlow t z)) volume 0 1 :=
    (continuous_const.mul (hL.comp hflow)).intervalIntegrable
    (μ := volume) (0 : ℝ) 1
  have iR : IntervalIntegrable (fun t ↦ δ * R (planarHopfFlow t z)) volume 0 1 :=
    (continuous_const.mul (hR.comp hflow)).intervalIntegrable
    (μ := volume) (0 : ℝ) 1
  have iD : IntervalIntegrable (fun t ↦ δ ^ 2 * D (planarHopfFlow t z)) volume 0 1 :=
    (continuous_const.mul (hD.comp hflow)).intervalIntegrable
    (μ := volume) (0 : ℝ) 1
  have he : (fun w ↦ ⟪freeDisplacementOldVector P Q η δ da dn w,
      freeDisplacementActiveVector Q η δ a n w⟫) =
      (fun w ↦ ((B w + δ * L w) + δ * R w) + δ ^ 2 * D w) := by
    funext w
    dsimp only [freeDisplacementOldVector, freeDisplacementVector,
      freeDisplacementActiveVector, B, L, R, D]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, matrix_action_inner_orthogonal (Q w) (hSO w), hnormal]
    ring
  rw [he]
  unfold orbitAverage
  change (∫ t in (0 : ℝ)..1,
    ((B (planarHopfFlow t z) + δ * L (planarHopfFlow t z)) +
      δ * R (planarHopfFlow t z)) + δ ^ 2 * D (planarHopfFlow t z)) = 0
  rw [intervalIntegral.integral_add ((iB.add iL).add iR) iD,
    intervalIntegral.integral_add (iB.add iL) iR, intervalIntegral.integral_add iB iL,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change ((orbitAverage planarHopfFlow B z + δ * orbitAverage planarHopfFlow L z) +
    δ * orbitAverage planarHopfFlow R z) + δ ^ 2 * orbitAverage planarHopfFlow D z = 0
  rw [free_mixed_base_period_zero P Q hP hQ hperiod da a z,
    free_mixed_first_cross_period_zero P Q hP hQ hPQ hSO η hη da n horth z,
    free_mixed_second_cross_period_zero Q hSO η hmean dn a z,
    free_mixed_quadratic_period_zero Q hQ η hη hquad dn n z]
  ring

end GlobalEmbedding.Paper
