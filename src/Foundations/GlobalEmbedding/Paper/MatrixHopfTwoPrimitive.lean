import GlobalEmbedding.Paper.MatrixHopfThreeFrame
import GlobalEmbedding.Paper.MatrixScalarBase
import GlobalEmbedding.Paper.PlanarFreeCurve

/-!
# The actual two-dimensional block of the orthogonal primitive

Source: `main.tex`, prop:matrix, lines 335–338.
DAG: `matrix-hopf-two-primitive`. The actual P2=f0 I+f1 J is linear in f.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace GlobalEmbedding.Paper
variable {C : ℕ} [Fact (0 < C)]

/-- The literal real two-by-two matrix of complex multiplication by a planar
vector. Its entries are precisely a0 I+a1 J, as in the original source. -/
def matrixPlanarComplexification : Planar →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ !![a 0, -a 1; a 1, a 0]
      map_add' := by
        intro a b
        ext i j
        fin_cases i <;> fin_cases j <;> simp [add_comm]
      map_smul' := by
        intro r a
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_neg] }

/-- The original P2, constructed literally from the actual same f. -/
def matrixHopfTwoPrimitive (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) :
    Matrix (Fin 2) (Fin 2) ℝ := matrixPlanarComplexification (f z)

/-- The original Q2, constructed from the actual orbit derivative v=Xf. -/
def matrixHopfTwoFrame (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) :
    Matrix (Fin 2) (Fin 2) ℝ := matrixPlanarComplexification (orbitDeriv planarHopfFlow f z)

/-- The actual P2 is native smooth by its genuine linear construction. -/
theorem matrixHopfTwoPrimitive_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℝ) ∞
      (matrixHopfTwoPrimitive f) := matrixPlanarComplexification.contMDiff.comp hf.smooth

/-- The actual Q2 is native smooth by actual native velocity smoothness and its
same genuine real continuous-linear complexification. -/
theorem matrixHopfTwoFrame_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℝ) ∞
      (matrixHopfTwoFrame f) := matrixPlanarComplexification.contMDiff.comp
        (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth)

/-- The actual derivative of the actual linear P2 is the actual Q2. -/
theorem matrixHopfTwoPrimitive_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixHopfTwoPrimitive f) z = matrixHopfTwoFrame f z := by
  have hh := matrixPlanarComplexification.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf.smooth 0 z)
  simpa only [matrixHopfTwoPrimitive, matrixHopfTwoFrame, orbitDeriv,
    planarHopfFlow_zero, Function.comp_def] using hh.deriv

/-- The actual unit velocity gives true SO(2), with orientation one, for the
literal complex multiplication matrix. -/
theorem matrixHopfTwoFrame_mem_SO (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    matrixHopfTwoFrame f z ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  change !![orbitDeriv planarHopfFlow f z 0, -orbitDeriv planarHopfFlow f z 1;
    orbitDeriv planarHopfFlow f z 1, orbitDeriv planarHopfFlow f z 0] ∈ _
  rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, rfl, ?_⟩
  have hh := congrArg (fun r : ℝ ↦ r ^ 2) (hf.unit_speed z)
  simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow, neg_sq] using hh

/-- The actual Q2 mean is zero by the actual derivative identity and native
periodic FTC for the same constructed P2. -/
theorem matrixHopfTwoFrame_average_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (matrixHopfTwoFrame f) z = 0 := by
  have hh := matrix_orbitDeriv_average_zero (planarHopfSmoothFlow C)
    (matrixHopfTwoPrimitive f) (matrixHopfTwoPrimitive_contMDiff f hf) z
  have he : orbitDeriv planarHopfFlow (matrixHopfTwoPrimitive f) = matrixHopfTwoFrame f :=
    funext (matrixHopfTwoPrimitive_orbitDeriv f hf)
  simpa only [planarHopfSmoothFlow, he] using hh

/-- Actual differentiation of the true Q2 is the complexification of the true
acceleration. This is a genuine continuous-linear chain rule on the actual flow. -/
theorem matrixHopfTwoFrame_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixHopfTwoFrame f) z =
      matrixPlanarComplexification (planarOrbitCurvature planarHopfFlow f z •
        planarQuarterTurn (orbitDeriv planarHopfFlow f z)) := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hh := matrixPlanarComplexification.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add (orbitDeriv planarHopfFlow f) hv 0 z)
  simp only [planarHopfFlow_zero, hf.acceleration] at hh
  simpa only [matrixHopfTwoFrame, orbitDeriv, Function.comp_def] using hh.deriv

/-- The actual XQ2 vanishes wherever the actual curvature vanishes. -/
theorem matrixHopfTwoFrame_orbitDeriv_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C)
    (hz : planarOrbitCurvature planarHopfFlow f z = 0) :
    orbitDeriv planarHopfFlow (matrixHopfTwoFrame f) z = 0 := by
  rw [matrixHopfTwoFrame_orbitDeriv f hf z, hz, zero_smul, map_zero]

/-- The actual derivative of the original quadratic potential is the actual
position/velocity dot product. Reuse the accepted genuine paraboloid lift chain
rule and project its actual last coordinate; no norm derivative is postulated. -/
theorem matrixHopf_scalarPotential_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixScalarPotential f) z =
      f z 0 * orbitDeriv planarHopfFlow f z 0 + f z 1 * orbitDeriv planarHopfFlow f z 1 := by
  have hd := planarQuadraticLift_hasDerivAt
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf.smooth 0 z)
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 3) 2).hasFDerivAt.comp_hasDerivAt 0 hd
  have he : (fun t : ℝ ↦ planarQuadraticLift (f (planarHopfFlow t z)) 2) =
      fun t : ℝ ↦ matrixScalarPotential f (planarHopfFlow t z) := by
    funext t
    exact planarQuadraticLift_last _
  change HasDerivAt (fun t : ℝ ↦ planarQuadraticLift (f (planarHopfFlow t z)) 2)
    (planarLiftVelocity (f (planarHopfFlow 0 z))
      (orbitDeriv planarHopfFlow f (planarHopfFlow 0 z)) 2) 0 at hh
  rw [he] at hh
  simpa [orbitDeriv, planarHopfFlow_zero, planarLiftVelocity] using hh.deriv

/-- The actual P2ᵀQ2 period vanishes. Its genuine diagonal entries are X(|f|²/2),
whose actual mean is zero by periodic FTC, and its off-diagonal entries are the
original signed area and its negative, whose actual means are zero. -/
theorem matrixHopfTwoPrimitive_period_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow
      (fun y ↦ (matrixHopfTwoPrimitive f y).transpose * matrixHopfTwoFrame f y) z = 0 := by
  have hφ := matrix_orbitDeriv_average_zero (planarHopfSmoothFlow C) (matrixScalarPotential f)
    (matrixScalarPotential_contMDiff f hf.smooth) z
  have he : orbitDeriv planarHopfFlow (matrixScalarPotential f) = fun y ↦
      f y 0 * orbitDeriv planarHopfFlow f y 0 + f y 1 * orbitDeriv planarHopfFlow f y 1 :=
    funext (matrixHopf_scalarPotential_orbitDeriv f hf)
  simp only [planarHopfSmoothFlow, he] at hφ
  have harea := hf.signed_area z
  have hc : Continuous (fun t : ℝ ↦ (matrixHopfTwoPrimitive f (planarHopfFlow t z)).transpose *
      matrixHopfTwoFrame f (planarHopfFlow t z)) :=
    ((matrixHopfTwoPrimitive_contMDiff f hf).continuous.matrix_transpose.matrix_mul
      (matrixHopfTwoFrame_contMDiff f hf).continuous).comp
        ((planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const))
  ext i j
  rw [matrix_orbitAverage_apply planarHopfFlow _ z hc]
  fin_cases i <;> fin_cases j
  · simpa [matrixHopfTwoPrimitive, matrixHopfTwoFrame, matrixPlanarComplexification,
      Matrix.mul_apply, Fin.sum_univ_two, orbitAverage, add_comm] using hφ
  · have hh : orbitAverage planarHopfFlow (fun y ↦
        -(f y 0 * orbitDeriv planarHopfFlow f y 1 -
          f y 1 * orbitDeriv planarHopfFlow f y 0)) z = 0 := by
      simpa only [orbitAverage, intervalIntegral.integral_neg, neg_zero] using congrArg Neg.neg harea
    simpa [matrixHopfTwoPrimitive, matrixHopfTwoFrame, matrixPlanarComplexification,
      Matrix.mul_apply, Fin.sum_univ_two, orbitAverage, sub_eq_add_neg, neg_add_rev, add_comm] using hh
  · simpa [matrixHopfTwoPrimitive, matrixHopfTwoFrame, matrixPlanarComplexification,
      Matrix.mul_apply, Fin.sum_univ_two, orbitAverage, sub_eq_add_neg, add_comm] using harea
  · simpa [matrixHopfTwoPrimitive, matrixHopfTwoFrame, matrixPlanarComplexification,
      Matrix.mul_apply, Fin.sum_univ_two, orbitAverage, add_comm] using hφ

/-- The literal standard planar quarter-turn matrix in the source. -/
def matrixPlanarSkew : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Unit planar velocity gives exactly κJ for the genuine transpose connection
of complex multiplication. Expand the literal two-by-two product and use the
actual Euclidean unit identity, retaining the source's orientation signs. -/
theorem matrixPlanarComplexification_connection (a : Planar) (κ : ℝ) (ha : ‖a‖ = 1) :
    (matrixPlanarComplexification a).transpose *
      matrixPlanarComplexification (κ • planarQuarterTurn a) = κ • matrixPlanarSkew := by
  have hu := congrArg (fun r : ℝ ↦ r ^ 2) ha
  have hu' : a 0 ^ 2 + a 1 ^ 2 = 1 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using hu
  have hk := congrArg (fun r : ℝ ↦ κ * r) hu'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixPlanarComplexification, matrixPlanarSkew, planarQuarterTurn,
      Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- The actual Q2ᵀXQ2 is precisely the actual curvature times the fixed source
skew line. This is the real fixed-V coordinate identity used by all even blocks. -/
theorem matrixHopfTwoFrame_connection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    (matrixHopfTwoFrame f z).transpose * orbitDeriv planarHopfFlow (matrixHopfTwoFrame f) z =
      planarOrbitCurvature planarHopfFlow f z • matrixPlanarSkew := by
  rw [matrixHopfTwoFrame_orbitDeriv f hf z]
  exact matrixPlanarComplexification_connection _ _ (hf.unit_speed z)

/-- The complete original first three matrix conclusions in dimension two hold
for the literal source P2, with Q literally XP2, and actual XQ vanishes on κ=0. -/
theorem matrix_hopf_two_orthogonal_primitive (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) :
    let P := matrixHopfTwoPrimitive f
    let Q := orbitDeriv planarHopfFlow P
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℝ) ∞ P ∧
      (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) ∧
      (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow (fun y ↦ (P y).transpose * Q y) z = 0) ∧
      (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 → orbitDeriv planarHopfFlow Q z = 0) := by
  have he : orbitDeriv planarHopfFlow (matrixHopfTwoPrimitive f) = matrixHopfTwoFrame f :=
    funext (matrixHopfTwoPrimitive_orbitDeriv f hf)
  dsimp only
  rw [he]
  exact ⟨matrixHopfTwoPrimitive_contMDiff f hf, matrixHopfTwoFrame_mem_SO f hf,
    matrixHopfTwoFrame_average_zero f hf, matrixHopfTwoPrimitive_period_zero f hf,
    matrixHopfTwoFrame_orbitDeriv_zero f hf⟩

#print axioms matrix_hopf_two_orthogonal_primitive
#print axioms matrixHopfTwoFrame_connection
#print axioms matrixPlanarComplexification_connection
#print axioms matrixHopf_scalarPotential_orbitDeriv
#print axioms matrixHopfTwoPrimitive_period_zero
#print axioms matrixHopfTwoPrimitive_contMDiff
#print axioms matrixHopfTwoPrimitive_orbitDeriv
#print axioms matrixHopfTwoFrame_mem_SO
#print axioms matrixHopfTwoFrame_average_zero
#print axioms matrixHopfTwoFrame_orbitDeriv
#print axioms matrixHopfTwoFrame_orbitDeriv_zero
end GlobalEmbedding.Paper
