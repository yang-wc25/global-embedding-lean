import GlobalEmbedding.Paper.FreeMixedCoordinatePeriod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Actual stationary orthogonal acceleration and exact active pivot

Source: `main.tex`, thm:free, equation(4.6), lines461–470.
DAG: free-active-pivot-identity. W3 recorded exclusive ownership before edits.
The literal displacement and its first active derivative are W2's canonical objects.
-/
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise RealInnerProductSpace
namespace GlobalEmbedding.Paper
variable {C d : ℕ}

local instance freeActivePivotMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable [Fact (0 < C)]

/-- Differentiate the actual constant orthogonal column pairings once. -/
theorem free_orthogonal_first_pair
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (a b : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q z) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) b⟫ +
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q z) b⟫ = 0 := by
  have ha := free_matrix_action_hasDerivAt Q hQ a z
  have hb := free_matrix_action_hasDerivAt Q hQ b z
  have hh := ha.inner ℝ hb
  have he : (fun t : ℝ ↦
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q (planarHopfFlow t z)) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q (planarHopfFlow t z)) b⟫) =
      (fun _ ↦ ⟪a, b⟫) := funext (fun t ↦ matrix_action_inner_orthogonal _ (horth _) a b)
  rw [he] at hh
  simpa only [planarHopfFlow_zero, add_comm] using hh.unique (hasDerivAt_const 0 ⟪a, b⟫)

/-- At actual stationary Q, the genuine second derivative obeys the skew
bilinear identity. It is obtained by differentiating the first identity, not by
assuming an acceleration matrix or a formal derivative rule. -/
theorem free_orthogonal_second_pair_zero
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (a b : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C)
    (hz : orbitDeriv planarHopfFlow Q z = 0) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) b⟫ +
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) b⟫ = 0 := by
  have hXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have ha := free_matrix_action_hasDerivAt Q hQ a z
  have hb := free_matrix_action_hasDerivAt Q hQ b z
  have hXa := free_matrix_action_hasDerivAt _ hXQ a z
  have hXb := free_matrix_action_hasDerivAt _ hXQ b z
  have hh := (hXa.inner ℝ hb).fun_add (ha.inner ℝ hXb)
  have he : (fun t : ℝ ↦
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q (planarHopfFlow t z)) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q (planarHopfFlow t z)) b⟫ +
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q (planarHopfFlow t z)) a,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q (planarHopfFlow t z)) b⟫) =
      (fun _ ↦ 0) := funext (fun t ↦ free_orthogonal_first_pair Q hQ horth a b _)
  rw [he] at hh
  have hzero := hh.unique (hasDerivAt_const 0 (0 : ℝ))
  simpa only [planarHopfFlow_zero, hz, map_zero, zero_apply,
    inner_zero_left, inner_zero_right, zero_add, add_zero] using hzero

/-- The actual matrix Q-transpose times X²Q is skew wherever the actual XQ
vanishes. This is a matrix transpose identity, not merely a numerical pivot. -/
theorem free_orthogonal_second_derivative_skew
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (z : PlanarHopfSphere C) (hz : orbitDeriv planarHopfFlow Q z = 0) :
    ((Q z).transpose * orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z).transpose =
      -((Q z).transpose * orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
  let D := orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z
  have ht (M : Matrix (Fin d) (Fin d) ℝ) : L M.transpose = (L M).adjoint := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      ContinuousLinearMap.star_eq_adjoint] using map_star L M
  have hsum : L (D.transpose * Q z + (Q z).transpose * D) = 0 := by
    apply ContinuousLinearMap.ext
    intro b
    apply ext_inner_left ℝ
    intro a
    rw [zero_apply, inner_zero_right]
    rw [map_add, map_mul, map_mul, ht, ht]
    change ⟪a, (L D).adjoint (L (Q z) b) + (L (Q z)).adjoint (L D b)⟫ = 0
    rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    exact free_orthogonal_second_pair_zero Q hQ horth a b z hz
  have hs : D.transpose * Q z + (Q z).transpose * D = 0 := by
    apply L.injective
    change L (D.transpose * Q z + (Q z).transpose * D) = L 0
    rw [map_zero]
    exact hsum
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hs

/-- The diagonal consequence of the genuine skew second-derivative pairing. -/
theorem free_orthogonal_second_self_pair_zero
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C)
    (hz : orbitDeriv planarHopfFlow Q z = 0) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) n,
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) n⟫ = 0 := by
  have hh := free_orthogonal_second_pair_zero Q hQ horth n n z hz
  rw [real_inner_comm] at hh
  linarith

/-- Differentiate W2's literal active coordinate vector once more. At actual
XQ=0 and X²eta=1 it factors as delta*(Q+eta X²Q)n, including delta=0. -/
theorem free_active_second_vector_factor
    (Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C)
    (hz : orbitDeriv planarHopfFlow Q z = 0)
    (he : orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) :
    orbitDeriv planarHopfFlow (freeDisplacementActiveVector Q η δ a n) z =
      δ • (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) n + η z •
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) n) := by
  have hXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have hXη := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) η hη
  have hqa := free_matrix_action_hasDerivAt Q hQ a z
  have hqn := free_matrix_action_hasDerivAt Q hQ n z
  have hXqn := free_matrix_action_hasDerivAt _ hXQ n z
  have hηd := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add η hη 0 z
  have hXηd := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add _ hXη 0 z
  have hh := hqa.fun_add (((hXηd.smul hqn).fun_add (hηd.smul hXqn)).const_smul δ)
  have hformula : orbitDeriv planarHopfFlow (freeDisplacementActiveVector Q η δ a n) z =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q z) a + δ •
        (orbitDeriv planarHopfFlow η z •
            Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q z) n +
          orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z •
            Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) n +
          (η z • Matrix.toEuclideanCLM (𝕜 := ℝ)
              (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) n +
            orbitDeriv planarHopfFlow η z •
              Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q z) n)) := by
    simpa only [orbitDeriv, freeDisplacementActiveVector, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply', planarHopfFlow_zero] using hh.deriv
  simpa only [hz, he, map_zero, zero_apply, smul_zero, zero_add, add_zero, one_smul]
    using hformula

/-- The second derivative of the same canonical actual displacement V has the
zero-curvature factor used in the uniform projection argument. -/
theorem free_active_second_displacement_factor
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) (z : PlanarHopfSphere C)
    (hz : orbitDeriv planarHopfFlow Q z = 0)
    (he : orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) :
    orbitDeriv planarHopfFlow
      (orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ a n)) z =
      δ • (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) n + η z •
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) z) n) := by
  have hh : orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ a n) =
      freeDisplacementActiveVector Q η δ a n :=
    funext (freeDisplacementVector_orbitDeriv P Q hP hQ hPQ η hη δ a n)
  rw [hh]
  exact free_active_second_vector_factor Q hQ η hη δ a n z hz he

/-- Exact original active pivot (4.6) for the same actual P,Q,eta and unit n.
Stationarity and X²eta=1 are the honest original matrix zero-curvature outputs;
no desired skew identity or pivot is assumed. -/
theorem free_active_pivot_identity
    (P Q : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (δ : ℝ) (a n : EuclideanSpace ℝ (Fin d)) (hn : ‖n‖ = 1)
    (z : PlanarHopfSphere C) (hz : orbitDeriv planarHopfFlow Q z = 0)
    (he : orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z) n,
      orbitDeriv planarHopfFlow
        (orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ a n)) z⟫ = δ := by
  rw [free_active_second_displacement_factor P Q hP hQ hPQ η hη δ a n z hz he,
    real_inner_smul_right, inner_add_right, real_inner_smul_right,
    free_orthogonal_second_self_pair_zero Q hQ horth n z hz, mul_zero, add_zero,
    matrix_action_inner_orthogonal _ (horth z) n n, real_inner_self_eq_norm_sq, hn]
  simp

end GlobalEmbedding.Paper
