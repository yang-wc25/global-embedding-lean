import GlobalEmbedding.Paper.MatrixFinitePositiveOrbitBumps
import GlobalEmbedding.Paper.MatrixExponentialMomentSmoothInverse
import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import GlobalEmbedding.Paper.MatrixManifoldFlatCurvatureCutoff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual positive flat moment densities

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines345–353, equation(3.5).
The density and square root are explicit smooth multiples of the actual flat cutoff.
-/

noncomputable section
open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

namespace GlobalEmbedding.Paper

section FlatFactor
variable {N Q : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]

/-- The literal density from the actual curvature cutoff and a positive smooth factor. -/
def matrixFlatDensity (κ B : Q → ℝ) (q : Q) : ℝ :=
  expNegInvGlue (κ q ^ 2) ^ 2 * B q

/-- The literal smooth square root, using positivity before taking a square root. -/
def matrixFlatDensitySqrt (κ B : Q → ℝ) (q : Q) : ℝ :=
  expNegInvGlue (κ q ^ 2) * Real.sqrt (B q)

omit [IsManifold 𝓘(ℝ, N) ∞ Q] in
/-- Strict positivity of the actual factor gives native smoothness of its square root. -/
theorem matrix_positive_factor_sqrt_contMDiff (B : Q → ℝ)
    (hB : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ B) (hpos : ∀ q, 0 < B q) :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ (fun q ↦ Real.sqrt (B q)) := by
  intro q
  exact (Real.contDiffAt_sqrt (hpos q).ne').contMDiffAt.comp q (hB q)

/-- Both explicit factors are native smooth and fully flat; the square identity is literal. -/
theorem matrix_flat_density_properties (κ B : Q → ℝ)
    (hκ : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ κ)
    (hB : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ B) (hpos : ∀ q, 0 < B q) :
    ManifoldFlatOn (I := 𝓘(ℝ, N)) (matrixFlatDensity κ B) {q | κ q = 0} ∧
    ManifoldFlatOn (I := 𝓘(ℝ, N)) (matrixFlatDensitySqrt κ B) {q | κ q = 0} ∧
    (∀ q, 0 ≤ matrixFlatDensity κ B q) ∧ (∀ q, 0 ≤ matrixFlatDensitySqrt κ B q) ∧
    (∀ q, matrixFlatDensitySqrt κ B q ^ 2 = matrixFlatDensity κ B q) ∧
    (∀ q, κ q ≠ 0 → 0 < matrixFlatDensity κ B q) := by
  have hc : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞
      (fun q ↦ expNegInvGlue (κ q ^ 2)) :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  have hs := matrix_positive_factor_sqrt_contMDiff B hB hpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : matrixFlatDensity κ B =
        fun q ↦ expNegInvGlue (κ q ^ 2) • (expNegInvGlue (κ q ^ 2) * B q) := by
      funext q
      simp only [matrixFlatDensity, smul_eq_mul, pow_two, mul_assoc]
    rw [heq]
    exact manifold_flat_curvature_cutoff_smul κ hκ
      (fun q ↦ expNegInvGlue (κ q ^ 2) * B q) (hc.mul hB)
  · exact manifold_flat_curvature_cutoff_smul κ hκ (fun q ↦ Real.sqrt (B q)) hs
  · intro q
    exact mul_nonneg (sq_nonneg _) (hpos q).le
  · intro q
    exact mul_nonneg (expNegInvGlue.nonneg _) (Real.sqrt_nonneg _)
  · intro q
    dsimp [matrixFlatDensitySqrt, matrixFlatDensity]
    rw [mul_pow, Real.sq_sqrt (hpos q).le]
  · intro q hq
    exact mul_pos (sq_pos_of_pos (expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hq))) (hpos q)

/-- An actual nonnegative flat square root makes the literal square root of twice the density
fully flat, even where the density vanishes. -/
theorem manifold_flat_sqrt_two_of_nonnegative_square (ρ σ : Q → ℝ) (Z : Set Q)
    (hσ : ManifoldFlatOn (I := 𝓘(ℝ, N)) σ Z) (hn : ∀ q, 0 ≤ σ q)
    (hsq : ∀ q, σ q ^ 2 = ρ q) :
    ManifoldFlatOn (I := 𝓘(ℝ, N)) (fun q ↦ Real.sqrt (2 * ρ q)) Z := by
  have heq : (fun q ↦ Real.sqrt (2 * ρ q)) = fun q ↦ σ q • Real.sqrt 2 := by
    funext q
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← hsq q, Real.sqrt_sq (hn q)]
    exact mul_comm _ _
  rw [heq]
  exact manifold_flat_on_smul hσ (fun _ ↦ Real.sqrt 2) contMDiff_const

end FlatFactor

section ExponentialFactor
variable {ι E N Q : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [TopologicalSpace Q] [ChartedSpace N Q] [IsManifold 𝓘(ℝ, N) ∞ Q]

/-- The literal basic positive exponential coefficient uses the actual moment inverse. -/
def matrixDensityCoefficient (v : Q → ι → E) (y : Q → E) (i : ι) (q : Q) : ℝ :=
  Real.exp ⟪v q i, matrixExponentialMomentInverse (v q) (y q)⟫

/-- The actual positive factor is the finite exponential sum weighted by squared bumps. -/
def matrixDensityFactor (v : Q → ι → E) (y : Q → E) (h : ι → Q → ℝ) (q : Q) : ℝ :=
  ∑ i, matrixDensityCoefficient v y i q * h i q ^ 2

/-- Actual smooth basic moments determine native smooth exponential coefficients. -/
theorem matrixDensityCoefficient_contMDiff (v : Q → ι → E) (y : Q → E)
    (hv : ∀ i, ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ (fun q ↦ v q i))
    (hy : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ y)
    (hspan : ∀ q, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v q i, u⟫) (i : ι) :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ (matrixDensityCoefficient v y i) := by
  have hl := matrixExponentialMomentInverse_contMDiff v y hv hy hspan
  exact Real.contDiff_exp.contMDiff.comp
    ((contDiff_inner (𝕜 := ℝ)).contMDiff.comp ((hv i).prodMk_space hl))

/-- The actual finite exponential factor is native smooth. -/
theorem matrixDensityFactor_contMDiff (v : Q → ι → E) (y : Q → E) (h : ι → Q → ℝ)
    (hv : ∀ i, ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ (fun q ↦ v q i))
    (hy : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ y)
    (hspan : ∀ q, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v q i, u⟫)
    (hh : ∀ i, ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ (h i)) :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, ℝ) ∞ (matrixDensityFactor v y h) :=
  contMDiff_finsetSum (fun i _ ↦ (matrixDensityCoefficient_contMDiff v y hv hy hspan i).mul
    ((hh i).pow 2))

omit [Nonempty ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ N]
    [IsManifold 𝓘(ℝ, N) ∞ Q] [TopologicalSpace Q] in
/-- The actual constant-one bump makes the actual finite factor strictly positive everywhere. -/
theorem matrixDensityFactor_pos (v : Q → ι → E) (y : Q → E) (h : ι → Q → ℝ)
    (h0 : ∃ i, ∀ q, h i q = 1) (q : Q) : 0 < matrixDensityFactor v y h q := by
  classical
  obtain ⟨i, hi⟩ := h0
  apply Finset.sum_pos' (fun j _ ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  exact ⟨i, Finset.mem_univ _, by simp only [hi q, one_pow, mul_one]; exact Real.exp_pos _⟩

omit [Nonempty ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ N]
    [IsManifold 𝓘(ℝ, N) ∞ Q] [TopologicalSpace Q] in
/-- Each actual exponential coefficient is constant along the actual orbit. -/
theorem matrixDensityCoefficient_flow (R : ℝ → Q → Q) (v : Q → ι → E) (y : Q → E)
    (hv : ∀ t q i, v (R t q) i = v q i) (hy : ∀ t q, y (R t q) = y q)
    (i : ι) (t : ℝ) (q : Q) :
    matrixDensityCoefficient v y i (R t q) = matrixDensityCoefficient v y i q := by
  dsimp only [matrixDensityCoefficient]
  rw [hv t q i, matrixExponentialMomentInverse_flow R v y hv hy]

end ExponentialFactor

section HopfDensity
variable {C : ℕ} [Fact (0 < C)]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Basic exponential coefficients pull through the actual period integral to give exactly y. -/
theorem matrix_density_factor_moment (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E) (y : PlanarHopfSphere C → E)
    (h : ι → PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (hh : ∀ i, ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (h i))
    (hy : ∀ t z, y (planarHopfFlow t z) = y z)
    (hspan : ∀ z, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪matrixOrbitBumpMoment κ A (h i) z, u⟫)
    (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow
      (fun q ↦ matrixFlatDensity κ
        (matrixDensityFactor (fun w i ↦ matrixOrbitBumpMoment κ A (h i) w) y h) q • A q) z =
      y z := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let v : PlanarHopfSphere C → ι → E := fun w i ↦ matrixOrbitBumpMoment κ A (h i) w
  have hv : ∀ t q i, v (planarHopfFlow t q) i = v q i :=
    fun t q i ↦ matrixOrbitBumpMoment_flow κ A (h i) t q
  have hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun q ↦ expNegInvGlue (κ q ^ 2)) :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hInt (i : ι) : IntervalIntegrable
      (fun t ↦ matrixDensityCoefficient v y i z •
        ((expNegInvGlue (κ (planarHopfFlow t z) ^ 2) ^ 2 * h i (planarHopfFlow t z) ^ 2) •
          A (planarHopfFlow t z))) volume 0 1 := by
    have hw := (((hc.pow 2).mul ((hh i).pow 2)).smul hA).continuous.comp hR
    exact (continuous_const.smul hw).intervalIntegrable _ _
  change (∫ t in (0 : ℝ)..1,
    matrixFlatDensity κ (matrixDensityFactor v y h) (planarHopfFlow t z) •
      A (planarHopfFlow t z)) = y z
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i, matrixDensityCoefficient v y i z •
        ((expNegInvGlue (κ (planarHopfFlow t z) ^ 2) ^ 2 * h i (planarHopfFlow t z) ^ 2) •
          A (planarHopfFlow t z)) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [matrixFlatDensity, matrixDensityFactor, Finset.mul_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [matrixDensityCoefficient_flow planarHopfFlow v y hv hy, smul_smul]
      congr 1
      ring
    _ = ∑ i, ∫ t in (0 : ℝ)..1, matrixDensityCoefficient v y i z •
        ((expNegInvGlue (κ (planarHopfFlow t z) ^ 2) ^ 2 * h i (planarHopfFlow t z) ^ 2) •
          A (planarHopfFlow t z)) :=
      intervalIntegral.integral_finsetSum (fun i _ ↦ hInt i)
    _ = ∑ i, matrixDensityCoefficient v y i z • v z i := by
      simp only [intervalIntegral.integral_smul]
      rfl
    _ = y z := matrixExponentialMomentInverse_moment (v z) (hspan z) (y z)

/-- Every actual smooth basic moment is realized by an actual nonnegative native smooth density
with an actual native smooth square root, both fully flat on the curvature-zero set and positive
off it. The finite bumps and actual minimizer are constructed inside the proof. -/
theorem matrix_positive_moment_density (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E) (y : PlanarHopfSphere C → E)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (hy : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ y)
    (hybasic : ∀ t z, y (planarHopfFlow t z) = y z)
    (hspan : ∀ z, ∀ u : E, u ≠ 0 → ∃ t : ℝ,
      κ (planarHopfFlow t z) ≠ 0 ∧ 0 < ⟪A (planarHopfFlow t z), u⟫) :
    ∃ ρ σ : PlanarHopfSphere C → ℝ,
      ManifoldFlatOn (I := planarHopfModel C) ρ {z | κ z = 0} ∧
      ManifoldFlatOn (I := planarHopfModel C) σ {z | κ z = 0} ∧
      (∀ z, 0 ≤ ρ z) ∧ (∀ z, 0 ≤ σ z) ∧ (∀ z, σ z ^ 2 = ρ z) ∧
      (∀ z, κ z ≠ 0 → 0 < ρ z) ∧ (∀ z, κ z ≠ 0 → 0 < σ z) ∧
      ∀ z, orbitAverage planarHopfFlow (fun w ↦ ρ w • A w) z = y z := by
  classical
  obtain ⟨H, h0, hH, hsupport⟩ := matrix_finite_positive_orbit_bumps κ A hκ hA hspan
  let J : Type := ↥H
  let : Fintype J := inferInstanceAs (Fintype ↥H)
  let : Nonempty J := ⟨⟨fun _ ↦ 1, h0⟩⟩
  let h : J → PlanarHopfSphere C → ℝ := fun j ↦ j.1
  let v : PlanarHopfSphere C → J → E := fun z i ↦ matrixOrbitBumpMoment κ A (h i) z
  have hh (i : J) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (h i) := hH i.1 i.2
  have hv (i : J) : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ (fun z ↦ v z i) :=
    matrixOrbitBumpMoment_contMDiff κ A (h i) hκ hA (hh i)
  have hvs : ∀ z, ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v z i, u⟫ := by
    intro z u hu
    obtain ⟨g, hg, hi⟩ := hsupport z u hu
    exact ⟨⟨g, hg⟩, hi⟩
  let B := matrixDensityFactor v y h
  have hB : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ B :=
    matrixDensityFactor_contMDiff v y h hv hy hvs hh
  have hBp : ∀ z, 0 < B z := matrixDensityFactor_pos v y h
    ⟨⟨fun _ ↦ 1, h0⟩, fun _ ↦ rfl⟩
  obtain ⟨hρ, hσ, hρnonneg, hσnonneg, hsq, hρpos⟩ :=
    matrix_flat_density_properties κ B hκ hB hBp
  refine ⟨matrixFlatDensity κ B, matrixFlatDensitySqrt κ B,
    hρ, hσ, hρnonneg, hσnonneg, hsq, hρpos, ?_, ?_⟩
  · intro z hz
    exact mul_pos (expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hz))
      (Real.sqrt_pos.mpr (hBp z))
  · exact matrix_density_factor_moment κ A y h hκ hA hh hybasic hvs

/-- The scalar correction receives the literal sqrt(2*rho) with all native flat jets. -/
theorem matrix_positive_moment_density_sqrt_two (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E) (y : PlanarHopfSphere C → E)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (hy : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ y)
    (hybasic : ∀ t z, y (planarHopfFlow t z) = y z)
    (hspan : ∀ z, ∀ u : E, u ≠ 0 → ∃ t : ℝ,
      κ (planarHopfFlow t z) ≠ 0 ∧ 0 < ⟪A (planarHopfFlow t z), u⟫) :
    ∃ ρ : PlanarHopfSphere C → ℝ,
      ManifoldFlatOn (I := planarHopfModel C) ρ {z | κ z = 0} ∧
      (∀ z, 0 ≤ ρ z) ∧ (∀ z, κ z ≠ 0 → 0 < ρ z) ∧
      ManifoldFlatOn (I := planarHopfModel C) (fun z ↦ Real.sqrt (2 * ρ z)) {z | κ z = 0} ∧
      ∀ z, orbitAverage planarHopfFlow (fun w ↦ ρ w • A w) z = y z := by
  obtain ⟨ρ, σ, hρ, hσ, hnρ, hnσ, hsq, hpρ, _, havg⟩ :=
    matrix_positive_moment_density κ A y hκ hA hy hybasic hspan
  exact ⟨ρ, hρ, hnρ, hpρ,
    manifold_flat_sqrt_two_of_nonnegative_square ρ σ _ hσ hnσ hsq, havg⟩

end HopfDensity

#print axioms matrix_positive_moment_density_sqrt_two
#print axioms matrix_positive_moment_density
#print axioms matrix_density_factor_moment
#print axioms matrixDensityFactor_contMDiff
#print axioms matrixDensityFactor_pos
#print axioms matrix_flat_density_properties

end GlobalEmbedding.Paper
