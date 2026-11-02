import GlobalEmbedding.Paper.MatrixHopfThreeFrame
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# The literal three-dimensional primitive and its complete matrix period

Source: `main.tex`, prop:matrix, lines 319–338.
DAG: `matrix-hopf-three-primitive`. Native Q3 and actual orbit calculus are reused.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace GlobalEmbedding.Paper
variable {C : ℕ} [Fact (0 < C)]

/-- The paper's P3 is literally the accepted weighted orbit primitive of Q3. -/
def matrixHopfThreePrimitive (f : PlanarHopfSphere C → Planar)
    (θ : PlanarHopfSphere C → ℝ) : PlanarHopfSphere C → Matrix (Fin 3) (Fin 3) ℝ :=
  planarOrbitPrimitive planarHopfFlow (matrixHopfThreeFrame f θ)

/-- The literal constructed P3 is native smooth by the accepted actual compact
integral theorem, applied to the already proved actual smooth Q3. -/
theorem matrixHopfThreePrimitive_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 3) (Fin 3) ℝ) ∞
      (matrixHopfThreePrimitive f θ) := by
  exact planarOrbitPrimitive_contMDiff planarHopfFlow
    ((planarHopfFlow_contMDiff C).comp (contMDiff_snd.prodMk contMDiff_fst))
    _ (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ)

/-- The same actual P3 differentiates to Q3 whenever the actual Q3 has zero mean.
This is the previously proved genuine primitive identity on the actual action. -/
theorem matrixHopfThreePrimitive_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixHopfThreePrimitive f θ) z = matrixHopfThreeFrame f θ z := by
  apply planarOrbitPrimitive_orbitDeriv_of_average_zero planarHopfFlow
    planarHopfFlow_zero planarHopfFlow_add planarHopfFlow_one
  · exact (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  · exact hmean z

/-- The same literal P3 has zero actual mean when Q3 has zero actual mean. -/
theorem matrixHopfThreePrimitive_average_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (z : PlanarHopfSphere C) : orbitAverage planarHopfFlow (matrixHopfThreePrimitive f θ) z = 0 := by
  apply planarOrbitPrimitive_average_zero planarHopfFlow planarHopfFlow_add planarHopfFlow_one
  · exact (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  · exact hmean z

/-- An actual planar coordinate and the actual orbit derivative commute by the
real continuous-linear coordinate chain rule; no separate scalar jet is supplied. -/
theorem matrixHopf_coordinate_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (i : Fin 2) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (fun y ↦ f y i) z = orbitDeriv planarHopfFlow f z i := by
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 2) i).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf.smooth 0 z)
  simpa [orbitDeriv, planarHopfFlow_zero, Function.comp_def] using hh.deriv

/-- The actual first primitive column is the actual centered planar position,
with zero third coordinate. Apply the genuine reverse primitive identity to both
actual coordinate functions and take the corresponding literal matrix entries. -/
theorem matrixHopfThreePrimitive_first_column (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (z : PlanarHopfSphere C) :
    matrixHopfThreePrimitive f θ z 0 0 =
        f z 0 - orbitAverage planarHopfFlow (fun y ↦ f y 0) z ∧
      matrixHopfThreePrimitive f θ z 1 0 =
        f z 1 - orbitAverage planarHopfFlow (fun y ↦ f y 1) z ∧
      matrixHopfThreePrimitive f θ z 2 0 = 0 := by
  have hc : Continuous (fun t : ℝ ↦ matrixHopfThreeFrame f θ (planarHopfFlow t z)) :=
    (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have he (i : Fin 2) : orbitDeriv planarHopfFlow (fun y ↦ f y i) =
      fun y ↦ orbitDeriv planarHopfFlow f y i :=
    funext (matrixHopf_coordinate_orbitDeriv f hf i)
  have hcoord (i : Fin 2) :
      planarOrbitPrimitive planarHopfFlow (fun y ↦ orbitDeriv planarHopfFlow f y i) z =
        f z i - orbitAverage planarHopfFlow (fun y ↦ f y i) z := by
    have hh := matrix_primitive_orbitDeriv (E := ℝ) (planarHopfSmoothFlow C)
      (fun y ↦ f y i) ((EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 2) i).contMDiff.comp hf.smooth) z
    change planarOrbitPrimitive planarHopfFlow (orbitDeriv planarHopfFlow (fun y ↦ f y i)) z = _ at hh
    rw [he i] at hh
    exact hh
  constructor
  · rw [matrixHopfThreePrimitive, matrix_primitive_apply planarHopfFlow _ z hc 0 0]
    exact hcoord 0
  constructor
  · rw [matrixHopfThreePrimitive, matrix_primitive_apply planarHopfFlow _ z hc 1 0]
    exact hcoord 1
  · rw [matrixHopfThreePrimitive, matrix_primitive_apply planarHopfFlow _ z hc 2 0]
    simp [planarOrbitPrimitive, matrixHopfThreeFrame, matrixThreeFrame]

/-- The literal three-dimensional reflection transform is an actual continuous
linear map on the actual matrix space; finite-dimensional continuity is reused. -/
def matrixThreeReflectionOperator : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ]
    Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    ((mulRightLinearMap (Fin 3) ℝ matrixThreeColumnReflection).comp
      (mulLeftLinearMap (Fin 3) ℝ matrixThreeReflection))

/-- The literal column conjugation is an actual continuous linear matrix map. -/
def matrixThreeColumnConjugation : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ]
    Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    ((mulRightLinearMap (Fin 3) ℝ matrixThreeColumnReflection).comp
      (mulLeftLinearMap (Fin 3) ℝ matrixThreeColumnReflection))

/-- The actual P3 has the same literal two-sided reflection as Q3. The actual
flow commutes with its half-action, and the genuine reflection continuous linear
map commutes with the literal weighted Bochner integral. -/
theorem matrixHopfThreePrimitive_reflection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z) (z : PlanarHopfSphere C) :
    matrixHopfThreePrimitive f θ (-z) = matrixThreeReflection *
      matrixHopfThreePrimitive f θ z * matrixThreeColumnReflection := by
  let L := matrixThreeReflectionOperator
  have hc : Continuous (fun t : ℝ ↦ matrixHopfThreeFrame f θ (planarHopfFlow t z)) :=
    (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have he (t : ℝ) : matrixHopfThreeFrame f θ (planarHopfFlow t (-z)) =
      L (matrixHopfThreeFrame f θ (planarHopfFlow t z)) := by
    rw [← planarHopfFlow_half z, ← planarHopfFlow_add, add_comm t (1 / 2),
      planarHopfFlow_add, planarHopfFlow_half, matrixHopfThreeFrame_reflection f hf θ hodd]
    rfl
  have hh := L.intervalIntegral_comp_comm (μ := volume)
    (f := fun t : ℝ ↦ t • matrixHopfThreeFrame f θ (planarHopfFlow t z))
    ((continuous_id.smul hc).intervalIntegrable 0 1)
  change (∫ t in (0 : ℝ)..1, t • matrixHopfThreeFrame f θ (planarHopfFlow t (-z))) =
    L (∫ t in (0 : ℝ)..1, t • matrixHopfThreeFrame f θ (planarHopfFlow t z))
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro t _
  change t • matrixHopfThreeFrame f θ (planarHopfFlow t (-z)) =
    L (t • matrixHopfThreeFrame f θ (planarHopfFlow t z))
  rw [he, L.map_smul]

/-- The actual real reflection matrix is orthogonal. This is the literal
finite diagonal multiplication, with no hypothesis on any desired primitive. -/
theorem matrixThreeReflection_transpose_mul :
    matrixThreeReflection.transpose * matrixThreeReflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixThreeReflection, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The column reflection is symmetric, by its literal diagonal entries. -/
theorem matrixThreeColumnReflection_transpose :
    matrixThreeColumnReflection.transpose = matrixThreeColumnReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixThreeColumnReflection]

/-- Reflection of the actual P3ᵀQ3 integrand is precisely conjugation by D.
Transpose the actual P3 reflection, insert actual Q3 reflection, and cancel the
literal ambient reflection by its already proved true orthogonality. -/
theorem matrixHopfThreePrimitive_period_integrand_reflection
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z) (z : PlanarHopfSphere C) :
    (matrixHopfThreePrimitive f θ (-z)).transpose * matrixHopfThreeFrame f θ (-z) =
      matrixThreeColumnReflection *
        ((matrixHopfThreePrimitive f θ z).transpose * matrixHopfThreeFrame f θ z) *
          matrixThreeColumnReflection := by
  rw [matrixHopfThreePrimitive_reflection f hf θ hθ hodd z,
    matrixHopfThreeFrame_reflection f hf θ hodd z]
  calc
    _ = matrixThreeColumnReflection *
        ((matrixHopfThreePrimitive f θ z).transpose *
          (matrixThreeReflection.transpose * matrixThreeReflection) *
          matrixHopfThreeFrame f θ z) * matrixThreeColumnReflection := by
      simp only [Matrix.transpose_mul, matrixThreeColumnReflection_transpose,
        Matrix.mul_assoc]
    _ = _ := by rw [matrixThreeReflection_transpose_mul, Matrix.mul_one]

/-- The actual P3ᵀQ3 period has the literal D-conjugation symmetry. The original
average is invariant under the actual half-period, and genuine continuous-linear
conjugation commutes with the genuine period integral. -/
theorem matrixHopfThreePrimitive_period_reflection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow
        (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z =
      matrixThreeColumnReflection * orbitAverage planarHopfFlow
        (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z *
        matrixThreeColumnReflection := by
  let G := fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y
  let L := matrixThreeColumnConjugation
  have hc : Continuous (fun t : ℝ ↦ G (planarHopfFlow t z)) :=
    (((matrixHopfThreePrimitive_contMDiff f hf θ hθ).continuous.matrix_transpose).matrix_mul
      (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous).comp
        ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have he (t : ℝ) : G (planarHopfFlow t (-z)) = L (G (planarHopfFlow t z)) := by
    rw [← planarHopfFlow_half z, ← planarHopfFlow_add, add_comm t (1 / 2),
      planarHopfFlow_add, planarHopfFlow_half]
    exact matrixHopfThreePrimitive_period_integrand_reflection f hf θ hθ hodd _
  have hi : orbitAverage planarHopfFlow G (-z) = orbitAverage planarHopfFlow G z := by
    simpa only [planarHopfFlow_half] using matrix_orbitAverage_invariant planarHopfFlow
      planarHopfFlow_add planarHopfFlow_one G z (1 / 2)
  have hh := L.intervalIntegral_comp_comm (μ := volume)
    (f := fun t : ℝ ↦ G (planarHopfFlow t z)) (hc.intervalIntegrable 0 1)
  have hmean : orbitAverage planarHopfFlow G (-z) = L (orbitAverage planarHopfFlow G z) := by
    unfold orbitAverage
    rw [← hh]
    exact intervalIntegral.integral_congr (fun t _ ↦ he t)
  exact hi.symm.trans hmean

/-- The actual P3ᵀQ3 period is genuinely skew, using XP3=Q3 proved for the same
literal primitive and the accepted genuine periodic column-product FTC. -/
theorem matrixHopfThreePrimitive_period_skew (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (z : PlanarHopfSphere C) (i j : Fin 3) :
    orbitAverage planarHopfFlow
      (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z i j =
      -orbitAverage planarHopfFlow
        (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z j i := by
  have hh := matrix_primitive_period_skew (planarHopfSmoothFlow C) (matrixHopfThreePrimitive f θ)
    (matrixHopfThreePrimitive_contMDiff f hf θ hθ) z i j
  have he : orbitDeriv planarHopfFlow (matrixHopfThreePrimitive f θ) = matrixHopfThreeFrame f θ :=
    funext (matrixHopfThreePrimitive_orbitDeriv f hf θ hθ hmean)
  simpa only [planarHopfSmoothFlow, he] using hh

/-- A genuinely skew three-by-three matrix fixed by actual D-conjugation has
only its 12-entry left. If that entry is zero, finite diagonal sign arithmetic
and skew symmetry force the entire literal matrix to be zero. -/
theorem matrixThree_skew_reflection_zero (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hreflect : A = matrixThreeColumnReflection * A * matrixThreeColumnReflection)
    (h01 : A 0 1 = 0) : A = 0 := by
  have h02 := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B 0 2) hreflect
  have h12 := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B 1 2) hreflect
  simp [matrixThreeColumnReflection, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ] at h02 h12
  have h00 := hskew 0 0
  have h11 := hskew 1 1
  have h22 := hskew 2 2
  have h10 := hskew 1 0
  have h20 := hskew 2 0
  have h21 := hskew 2 1
  ext i j
  fin_cases i <;> fin_cases j
  · change A 0 0 = 0
    linarith
  · change A 0 1 = 0
    linarith
  · change A 0 2 = 0
    linarith
  · change A 1 0 = 0
    linarith
  · change A 1 1 = 0
    linarith
  · change A 1 2 = 0
    linarith
  · change A 2 0 = 0
    linarith
  · change A 2 1 = 0
    linarith
  · change A 2 2 = 0
    linarith


/-- The sole potentially remaining 12-period is minus the original fourth angle
moment. The actual first primitive column is f minus its actual basic average;
its constant corrections integrate to zero against the actual zero-mean Q3. -/
theorem matrixHopfThreePrimitive_period_zero_one (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow
      (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z 0 1 = 0 := by
  let Q := matrixHopfThreeFrame f θ
  let P := matrixHopfThreePrimitive f θ
  let c0 := orbitAverage planarHopfFlow (fun y ↦ f y 0) z
  let c1 := orbitAverage planarHopfFlow (fun y ↦ f y 1) z
  have hqc : Continuous (fun t : ℝ ↦ Q (planarHopfFlow t z)) :=
    (matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have hpc : Continuous (fun t : ℝ ↦ P (planarHopfFlow t z)) :=
    (matrixHopfThreePrimitive_contMDiff f hf θ hθ).continuous.comp
      ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have hgc := hpc.matrix_transpose.matrix_mul hqc
  have he (t : ℝ) : ((P (planarHopfFlow t z)).transpose * Q (planarHopfFlow t z)) 0 1 =
      -(matrixPlanarB f (planarHopfFlow t z) * Real.sin (θ (planarHopfFlow t z))) -
        c0 * Q (planarHopfFlow t z) 0 1 - c1 * Q (planarHopfFlow t z) 1 1 := by
    have hh := matrixHopfThreePrimitive_first_column f hf θ hθ (planarHopfFlow t z)
    have hb0 := matrix_orbitAverage_invariant planarHopfFlow planarHopfFlow_add
      planarHopfFlow_one (fun y ↦ f y 0) z t
    have hb1 := matrix_orbitAverage_invariant planarHopfFlow planarHopfFlow_add
      planarHopfFlow_one (fun y ↦ f y 1) z t
    change _ = _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    change P (planarHopfFlow t z) 0 0 * Q (planarHopfFlow t z) 0 1 +
      (P (planarHopfFlow t z) 1 0 * Q (planarHopfFlow t z) 1 1 +
        (P (planarHopfFlow t z) 2 0 * Q (planarHopfFlow t z) 2 1 + 0)) = _
    dsimp only [P]
    rw [hh.1, hh.2.1, hh.2.2, hb0, hb1, matrixPlanarB_coordinates]
    simp [Q, matrixHopfThreeFrame, matrixThreeFrame, c0, c1]
    ring
  have hq01 : (∫ t in (0 : ℝ)..1, Q (planarHopfFlow t z) 0 1) = 0 := by
    have hh := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B 0 1) (hmean z)
    rw [matrix_orbitAverage_apply planarHopfFlow _ z hqc] at hh
    exact hh
  have hq11 : (∫ t in (0 : ℝ)..1, Q (planarHopfFlow t z) 1 1) = 0 := by
    have hh := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ ↦ B 1 1) (hmean z)
    rw [matrix_orbitAverage_apply planarHopfFlow _ z hqc] at hh
    exact hh
  have hbc : Continuous (fun t : ℝ ↦ matrixPlanarB f (planarHopfFlow t z) *
      Real.sin (θ (planarHopfFlow t z))) :=
    (((matrix_planar_data_contMDiff f hf.smooth).2.2.1.continuous).mul
      (Real.continuous_sin.comp hθ.continuous)).comp
        ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  have hc01 : Continuous (fun t : ℝ ↦ Q (planarHopfFlow t z) 0 1) :=
    ((continuous_apply 1).comp ((continuous_apply 0).comp hqc))
  have hc11 : Continuous (fun t : ℝ ↦ Q (planarHopfFlow t z) 1 1) :=
    ((continuous_apply 1).comp ((continuous_apply 1).comp hqc))
  rw [matrix_orbitAverage_apply planarHopfFlow _ z hgc]
  change (∫ t in (0 : ℝ)..1, ((P (planarHopfFlow t z)).transpose * Q (planarHopfFlow t z)) 0 1) = 0
  calc
    _ = ∫ t in (0 : ℝ)..1,
        -(matrixPlanarB f (planarHopfFlow t z) * Real.sin (θ (planarHopfFlow t z))) -
          c0 * Q (planarHopfFlow t z) 0 1 - c1 * Q (planarHopfFlow t z) 1 1 := by
      exact intervalIntegral.integral_congr (fun t _ ↦ he t)
    _ = 0 := by
      rw [intervalIntegral.integral_sub (μ := volume)
        (f := fun t : ℝ ↦ -(matrixPlanarB f (planarHopfFlow t z) *
          Real.sin (θ (planarHopfFlow t z))) - c0 * Q (planarHopfFlow t z) 0 1)
        (g := fun t : ℝ ↦ c1 * Q (planarHopfFlow t z) 1 1)
        ((hbc.neg.sub (hc01.const_mul c0)).intervalIntegrable 0 1)
        ((hc11.const_mul c1).intervalIntegrable 0 1),
        intervalIntegral.integral_sub (μ := volume)
          (f := fun t : ℝ ↦ -(matrixPlanarB f (planarHopfFlow t z) *
            Real.sin (θ (planarHopfFlow t z))))
          (g := fun t : ℝ ↦ c0 * Q (planarHopfFlow t z) 0 1)
          (hbc.neg.intervalIntegrable 0 1)
          ((hc01.const_mul c0).intervalIntegrable 0 1)]
      simp only [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        hq01, hq11, mul_zero, sub_zero]
      exact neg_eq_zero.mpr (hbsin z)

/-- The full actual P3ᵀQ3 period vanishes. Actual derivative/FTC makes it skew;
actual reflection gives D-conjugation; the fourth original moment kills its only
remaining 12-entry. Apply the complete literal matrix algebra cancellation. -/
theorem matrixHopfThreePrimitive_period_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hmean : ∀ z, orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow
      (fun y ↦ (matrixHopfThreePrimitive f θ y).transpose * matrixHopfThreeFrame f θ y) z = 0 := by
  exact matrixThree_skew_reflection_zero _
    (matrixHopfThreePrimitive_period_skew f hf θ hθ hmean z)
    (matrixHopfThreePrimitive_period_reflection f hf θ hθ hodd z)
    (matrixHopfThreePrimitive_period_zero_one f hf θ hθ hmean hbsin z)

/-- The original first three matrix conclusions in dimension three hold for the
same literal constructed P3, with Q literally XP3. The actual first three angle
moments give zero mean, the fourth gives the full PᵀQ period, and the actual
zero-angle-derivative condition gives XQ=0 on the actual curvature-zero set. -/
theorem matrix_hopf_three_orthogonal_primitive (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hcos : ∀ z, orbitAverage planarHopfFlow (fun y ↦ Real.cos (θ y)) z = 0)
    (htsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarT f y * Real.sin (θ y)) z = 0)
    (hscos : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarS f y * Real.cos (θ y)) z = 0)
    (hbsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarB f y * Real.sin (θ y)) z = 0)
    (hθzero : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow θ z = 0) :
    let P := matrixHopfThreePrimitive f θ
    let Q := orbitDeriv planarHopfFlow P
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 3) (Fin 3) ℝ) ∞ P ∧
      (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) ∧
      (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow (fun y ↦ (P y).transpose * Q y) z = 0) ∧
      (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 → orbitDeriv planarHopfFlow Q z = 0) := by
  have hmean := matrixHopfThreeFrame_average_zero f hf θ hθ hodd hcos htsin hscos
  have he : orbitDeriv planarHopfFlow (matrixHopfThreePrimitive f θ) = matrixHopfThreeFrame f θ :=
    funext (matrixHopfThreePrimitive_orbitDeriv f hf θ hθ hmean)
  dsimp only
  rw [he]
  exact ⟨matrixHopfThreePrimitive_contMDiff f hf θ hθ,
    matrixHopfThreeFrame_mem_SO f hf.unit_speed θ, hmean,
    matrixHopfThreePrimitive_period_zero f hf θ hθ hodd hmean hbsin,
    fun z hz ↦ matrixHopfThreeFrame_orbitDeriv_zero f hf θ hθ z hz (hθzero z hz)⟩

#print axioms matrix_hopf_three_orthogonal_primitive
#print axioms matrixHopfThreePrimitive_period_zero_one
#print axioms matrixHopfThreePrimitive_period_zero
#print axioms matrixHopfThreePrimitive_period_reflection
#print axioms matrixHopfThreePrimitive_period_skew
#print axioms matrixThree_skew_reflection_zero
#print axioms matrixHopfThreePrimitive_reflection
#print axioms matrixHopfThreePrimitive_period_integrand_reflection
#print axioms matrixHopfThreePrimitive_contMDiff
#print axioms matrixHopfThreePrimitive_orbitDeriv
#print axioms matrixHopfThreePrimitive_average_zero
#print axioms matrixHopfThreePrimitive_first_column
end GlobalEmbedding.Paper
