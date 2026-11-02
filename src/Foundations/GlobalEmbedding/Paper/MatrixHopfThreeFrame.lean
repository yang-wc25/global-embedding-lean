import GlobalEmbedding.Paper.MatrixOrbitCalculus
import GlobalEmbedding.Paper.MatrixThreeFrame
import GlobalEmbedding.Paper.MatrixNativePlanarProfiles
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.MatrixAngleNativeSmoothFlat

/-!
# The actual three-dimensional special orthogonal Hopf frame

Source: `main.tex`, prop:matrix, lines 303–338. DAG: `matrix-hopf-three-frame`.
The actual Q3 is built from the actual velocity of f and the actual scalar θ.
The later primitive is the same accepted weighted orbit integral.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace GlobalEmbedding.Paper

variable {C : ℕ} [Fact (0 < C)]

/-- The literal source Q3 on the actual native Hopf sphere. -/
def matrixHopfThreeFrame (f : PlanarHopfSphere C → Planar)
    (θ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrixThreeFrame (matrixPlanarS f z) (matrixPlanarT f z) (θ z)

/-- The actual Q3 is genuinely native smooth. The accepted actual planar velocity
profiles are smooth; every literal matrix entry is their product with sine or
cosine of the actual smooth angle. Finite Pi smoothness assembles these entries. -/
theorem matrixHopfThreeFrame_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin 3) (Fin 3) ℝ) ∞
      (matrixHopfThreeFrame f θ) := by
  have hs := (matrix_planar_data_contMDiff f hf).1
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have hsin := Real.contDiff_sin.contMDiff.comp hθ
  have hcos := Real.contDiff_cos.contMDiff.comp hθ
  apply contMDiff_pi_module_iff.mpr
  intro i
  apply contMDiff_pi_module_iff.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hs
  · exact ht.mul hsin
  · exact ht.mul hcos
  · exact ht
  · exact hs.neg.mul hsin
  · exact hs.neg.mul hcos
  · exact contMDiff_const
  · exact hcos
  · exact hsin.neg

omit [Fact (0 < C)] in
/-- The actual Q3 lies in the genuine special orthogonal matrix group at every
point. The accepted Euclidean unit-speed hypothesis gives exactly s²+t²=1;
apply the complete literal frame calculation. -/
theorem matrixHopfThreeFrame_mem_SO (f : PlanarHopfSphere C → Planar)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (θ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    matrixHopfThreeFrame f θ z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  apply matrixThreeFrame_mem_SO
  have hh := congrArg (fun r : ℝ ↦ r ^ 2) (hunit z)
  simpa only [matrixPlanarS, matrixPlanarT, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, one_pow] using hh

/-- The actual velocity of the literal Q3 is exactly its explicitly computed
matrix derivative. The genuine planar acceleration equation supplies both scalar
velocity derivatives, and ordinary chain rules supply the angle derivative. -/
theorem matrixHopfThreeFrame_orbitDeriv (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixHopfThreeFrame f θ) z =
      matrixThreeFrameVelocity (matrixPlanarS f z) (matrixPlanarT f z) (θ z)
        (planarOrbitCurvature planarHopfFlow f z) (orbitDeriv planarHopfFlow θ z) := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hd := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add (orbitDeriv planarHopfFlow f) hv 0 z
  have hs := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 2) 0).hasFDerivAt.comp_hasDerivAt 0 hd
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 2) 1).hasFDerivAt.comp_hasDerivAt 0 hd
  simp only [planarHopfFlow_zero, hf.acceleration] at hs ht
  have hs' : HasDerivAt (fun t ↦ matrixPlanarS f (planarHopfFlow t z))
      (-planarOrbitCurvature planarHopfFlow f z * matrixPlanarT f z) 0 := by
    simpa [matrixPlanarS, matrixPlanarT, planarQuarterTurn, Function.comp_def] using hs
  have ht' : HasDerivAt (fun t ↦ matrixPlanarT f (planarHopfFlow t z))
      (planarOrbitCurvature planarHopfFlow f z * matrixPlanarS f z) 0 := by
    exact ht
  have hθ' := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add θ hθ 0 z
  simp only [planarHopfFlow_zero] at hθ'
  have hh := matrixThreeFrame_hasDerivAt
    (s := fun t ↦ matrixPlanarS f (planarHopfFlow t z))
    (t := fun t ↦ matrixPlanarT f (planarHopfFlow t z))
    (θ := fun t ↦ θ (planarHopfFlow t z))
    (x := 0) (κ := planarOrbitCurvature planarHopfFlow f z)
    (a := orbitDeriv planarHopfFlow θ z)
    (by simpa only [planarHopfFlow_zero] using hs')
    (by simpa only [planarHopfFlow_zero] using ht') hθ' 
  simpa only [planarHopfFlow_zero, orbitDeriv, matrixHopfThreeFrame] using hh.deriv

/-- The true QᵀXQ on the whole actual sphere is the exact connection used for
angular cone and scalar moment construction; no independent skew field is given. -/
theorem matrixHopfThreeFrame_connection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (z : PlanarHopfSphere C) :
    (matrixHopfThreeFrame f θ z).transpose *
      orbitDeriv planarHopfFlow (matrixHopfThreeFrame f θ) z =
      matrixThreeConnection (θ z) (planarOrbitCurvature planarHopfFlow f z)
        (orbitDeriv planarHopfFlow θ z) := by
  rw [matrixHopfThreeFrame_orbitDeriv f hf θ hθ z]
  apply matrixThreeFrame_connection
  have hh := congrArg (fun r : ℝ ↦ r ^ 2) (hf.unit_speed z)
  simpa only [matrixPlanarS, matrixPlanarT, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, one_pow] using hh

/-- At zero curvature and zero actual angle derivative the genuine XQ is zero,
by the actual chain-rule formula, not by an assumption on the desired frame. -/
theorem matrixHopfThreeFrame_orbitDeriv_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ) (z : PlanarHopfSphere C)
    (hκ : planarOrbitCurvature planarHopfFlow f z = 0)
    (hθzero : orbitDeriv planarHopfFlow θ z = 0) :
    orbitDeriv planarHopfFlow (matrixHopfThreeFrame f θ) z = 0 := by
  rw [matrixHopfThreeFrame_orbitDeriv f hf θ hθ z, hκ, hθzero]
  exact matrixThreeFrameVelocity_zero _ _ _

/-- Actual differentiation commutes with the actual antipodal reflection of f.
Translate by the actual half-period and apply the already constructed genuine
linear isometry to the actual orbit curve; uniqueness of real derivatives gives
reflection of the actual velocity, including both coordinate parities. -/
theorem matrixHopf_velocity_reflection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow f (-z) = planarReflection (orbitDeriv planarHopfFlow f z) := by
  exact matrixAngleVelocity_reflection f hf.smooth hf.reflection z

/-- The actual Q3 obeys the exact two-sided ambient/column reflection identity.
Use actual velocity reflection and the actual odd angle in the literal frame. -/
theorem matrixHopfThreeFrame_reflection (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hodd : ∀ z, θ (-z) = -θ z) (z : PlanarHopfSphere C) :
    matrixHopfThreeFrame f θ (-z) = matrixThreeReflection *
      matrixHopfThreeFrame f θ z * matrixThreeColumnReflection := by
  simp only [matrixHopfThreeFrame, matrixPlanarS, matrixPlanarT,
    matrixHopf_velocity_reflection f hf z, planarReflection_apply_zero,
    planarReflection_apply_one, hodd]
  exact matrixThreeFrame_reflection _ _ _

/-- Actual velocity coordinates inherit the precise half-period parity. -/
theorem matrixHopf_velocity_coordinate_parity (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) :
    matrixPlanarS f (-z) = matrixPlanarS f z ∧
      matrixPlanarT f (-z) = -matrixPlanarT f z := by
  simp only [matrixPlanarS, matrixPlanarT, matrixHopf_velocity_reflection f hf z,
    planarReflection_apply_zero, planarReflection_apply_one, and_self]

/-- The actual first velocity component has zero mean, by genuine native periodic
FTC for f followed by its genuine Euclidean coordinate continuous linear map. -/
theorem matrixHopf_velocity_coordinate_average_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (z : PlanarHopfSphere C) (i : Fin 2) :
    orbitAverage planarHopfFlow (fun y ↦ orbitDeriv planarHopfFlow f y i) z = 0 := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hc : Continuous (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t z)) :=
    hv.continuous.comp ((planarHopfFlow_contMDiff C).continuous.comp
      (continuous_id.prodMk continuous_const))
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin 2) i).intervalIntegral_comp_comm (μ := volume)
    (hc.intervalIntegrable 0 1)
  have hz := matrix_orbitDeriv_average_zero (planarHopfSmoothFlow C) f hf.smooth z
  change (∫ t in (0 : ℝ)..1, orbitDeriv planarHopfFlow f (planarHopfFlow t z)) = 0 at hz
  rw [hz, map_zero] at hh
  exact hh

/-- The actual Q3 has zero matrix mean from precisely the first three original
angle equations and actual reflection. Each remaining nonzero uncontrolled entry
is odd under the genuine half-action; the first column is an actual derivative. -/
theorem matrixHopfThreeFrame_average_zero (f : PlanarHopfSphere C → Planar)
    (hf : MatrixPlanarSelectorProperties f) (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (hodd : ∀ z, θ (-z) = -θ z)
    (hcos : ∀ z, orbitAverage planarHopfFlow (fun y ↦ Real.cos (θ y)) z = 0)
    (htsin : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarT f y * Real.sin (θ y)) z = 0)
    (hscos : ∀ z, orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarS f y * Real.cos (θ y)) z = 0) (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (matrixHopfThreeFrame f θ) z = 0 := by
  have hsin : orbitAverage planarHopfFlow (fun y ↦ Real.sin (θ y)) z = 0 := by
    apply matrix_orbitAverage_half_odd_zero planarHopfFlow planarHopfFlow_add planarHopfFlow_one
    intro y
    simp only [planarHopfFlow_half, hodd, Real.sin_neg]
  have hssin : orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarS f y * Real.sin (θ y)) z = 0 := by
    apply matrix_orbitAverage_half_odd_zero planarHopfFlow planarHopfFlow_add planarHopfFlow_one
    intro y
    simp only [planarHopfFlow_half, (matrixHopf_velocity_coordinate_parity f hf y).1,
      hodd, Real.sin_neg, mul_neg]
  have htcos : orbitAverage planarHopfFlow
      (fun y ↦ matrixPlanarT f y * Real.cos (θ y)) z = 0 := by
    apply matrix_orbitAverage_half_odd_zero planarHopfFlow planarHopfFlow_add planarHopfFlow_one
    intro y
    simp only [planarHopfFlow_half, (matrixHopf_velocity_coordinate_parity f hf y).2,
      hodd, Real.cos_neg, neg_mul]
  have hq := matrixHopfThreeFrame_contMDiff f hf.smooth θ hθ
  have hc : Continuous (fun t : ℝ ↦ matrixHopfThreeFrame f θ (planarHopfFlow t z)) :=
    hq.continuous.comp ((planarHopfFlow_contMDiff C).continuous.comp
      (continuous_id.prodMk continuous_const))
  have hs := matrixHopf_velocity_coordinate_average_zero f hf z 0
  have ht := matrixHopf_velocity_coordinate_average_zero f hf z 1
  ext i j
  rw [matrix_orbitAverage_apply planarHopfFlow _ z hc i j]
  fin_cases i <;> fin_cases j
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using hs
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using htsin z
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using htcos
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using ht
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using hssin
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using hscos z
  · simp [matrixHopfThreeFrame, matrixThreeFrame, orbitAverage]
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using hcos z
  · simpa [matrixHopfThreeFrame, matrixThreeFrame, matrixPlanarS, matrixPlanarT,
      orbitAverage, intervalIntegral.integral_neg] using hsin

#print axioms matrixHopfThreeFrame_average_zero
#print axioms matrixHopf_velocity_coordinate_average_zero
#print axioms matrixHopf_velocity_reflection
#print axioms matrixHopfThreeFrame_reflection
#print axioms matrixHopfThreeFrame_orbitDeriv
#print axioms matrixHopfThreeFrame_connection
#print axioms matrixHopfThreeFrame_orbitDeriv_zero
#print axioms matrixHopfThreeFrame_contMDiff
#print axioms matrixHopfThreeFrame_mem_SO
end GlobalEmbedding.Paper
