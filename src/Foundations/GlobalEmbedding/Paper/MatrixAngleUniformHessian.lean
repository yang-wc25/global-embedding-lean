import GlobalEmbedding.Paper.MatrixAngleMomentCalculus
import GlobalEmbedding.Paper.MatrixAngleNativeSmoothFlat
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A frequency-independent bound on the actual coefficient Hessian

Source: `main.tex`, `prop:matrix`, lines307–315.
DAG node: `matrix-angle-uniform-hessian`; exclusive owner W2.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Topology NNReal
open Set Filter MeasureTheory

namespace GlobalEmbedding.Paper

variable {C : ℕ}

private theorem euclidean_four_norm_le_sum (v : MatrixAngleCoefficients) :
    ‖v‖ ≤ ∑ i : Fin 4, |v i| := by
  have he : v = ∑ i : Fin 4, EuclideanSpace.single i (v i) := by
    ext j
    simp [EuclideanSpace.single]
  calc
    ‖v‖ = ‖∑ i : Fin 4, EuclideanSpace.single i (v i)‖ := congrArg norm he
    _ ≤ ∑ i : Fin 4, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, |v i| := by simp [EuclideanSpace.single, PiLp.norm_single]

/-- A fixed actual amplitude bounds every angle, independently of its frequency. -/
def matrixAngleAmplitude (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) : ℝ :=
  1 + |orbitDeriv planarHopfFlow f z 1| + |orbitDeriv planarHopfFlow f z 0| +
    |matrixAngleNormalPosition f z|

/-- The actual values vector is bounded by the fixed amplitude at every scalar angle. -/
theorem matrixAngleMomentValues_norm_le (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) (θ : ℝ) :
    ‖matrixAngleMomentValues f θ z‖ ≤ matrixAngleAmplitude f z := by
  apply (euclidean_four_norm_le_sum _).trans
  simp only [Fin.sum_univ_four]
  change |Real.cos θ| + |orbitDeriv planarHopfFlow f z 1 * Real.sin θ| +
    |orbitDeriv planarHopfFlow f z 0 * Real.cos θ| +
    |matrixAngleNormalPosition f z * Real.sin θ| ≤ _
  simp only [abs_mul]
  exact add_le_add (add_le_add (add_le_add (Real.abs_cos_le_one θ)
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ)))
      (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ))

/-- The actual direction vector has the same frequency-independent amplitude bound. -/
theorem matrixAngleMomentDirection_norm_le (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) (θ : ℝ) :
    ‖matrixAngleMomentDirection f θ z‖ ≤ matrixAngleAmplitude f z := by
  apply (euclidean_four_norm_le_sum _).trans
  simp only [Fin.sum_univ_four]
  change |-Real.sin θ| + |orbitDeriv planarHopfFlow f z 1 * Real.cos θ| +
    |-(orbitDeriv planarHopfFlow f z 0) * Real.sin θ| +
    |matrixAngleNormalPosition f z * Real.cos θ| ≤ _
  simp only [abs_mul, abs_neg]
  exact add_le_add (add_le_add (add_le_add (Real.abs_sin_le_one θ)
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)))
      (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ)))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ))

/-- A bound on the fixed amplitude bounds the Lipschitz constant of the actual direction. -/
theorem matrixAngleMomentDirection_lipschitzWith (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) (M : ℝ≥0) (hM : matrixAngleAmplitude f z ≤ M) :
    LipschitzWith M (fun θ ↦ matrixAngleMomentDirection f θ z) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro θ
    exact (matrixAngleMomentDirection_hasDerivAt f z θ).differentiableAt
  · intro θ
    change ‖deriv (fun q ↦ matrixAngleMomentDirection f q z) θ‖ ≤ (M : ℝ)
    rw [(matrixAngleMomentDirection_hasDerivAt f z θ).deriv, norm_neg]
    exact (matrixAngleMomentValues_norm_le f z θ).trans hM

/-- The literal coefficient derivative integrand from the actual moment calculus. -/
def matrixAngleMomentCoefficientDerivative (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (a : MatrixAngleCoefficients) : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients :=
  matrixAngleCutoff κ z •
    (ContinuousLinearMap.toSpanSingleton ℝ
      (matrixAngleMomentDirection f (matrixAngleAnsatz f κ T a z) z)).comp
        (InnerProductSpace.toDual ℝ MatrixAngleCoefficients (matrixAngleBaseProfile f T z))

/-- The exact affine angle has the expected coefficient difference bound. -/
theorem matrixAngleAnsatz_sub_le (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (a b : MatrixAngleCoefficients) :
    |matrixAngleAnsatz f κ T a z - matrixAngleAnsatz f κ T b z| ≤
      |matrixAngleCutoff κ z| * ‖matrixAngleBaseProfile f T z‖ * ‖a - b‖ := by
  have he : matrixAngleAnsatz f κ T a z - matrixAngleAnsatz f κ T b z =
      matrixAngleCutoff κ z * ⟪matrixAngleBaseProfile f T z, a - b⟫ := by
    simp only [matrixAngleAnsatz, inner_sub_right]
    ring
  rw [he, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)

/-- The actual coefficient derivative integrand has a uniform Lipschitz bound in coefficients.
The only bounds here concern fixed actual amplitudes and the actual curvature cutoff. -/
theorem matrixAngleMomentCoefficientDerivative_sub_le (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (M R : ℝ≥0) (hM : matrixAngleAmplitude f z ≤ M)
    (hR : |matrixAngleCutoff κ z| ≤ R) (a b : MatrixAngleCoefficients) :
    ‖matrixAngleMomentCoefficientDerivative f κ T z a -
        matrixAngleMomentCoefficientDerivative f κ T z b‖ ≤
      ((R : ℝ) ^ 2 * (M : ℝ) ^ 3) * ‖a - b‖ := by
  let v := matrixAngleBaseProfile f T z
  let d := matrixAngleMomentDirection f (matrixAngleAnsatz f κ T a z) z -
    matrixAngleMomentDirection f (matrixAngleAnsatz f κ T b z) z
  have hv : ‖v‖ ≤ M := (matrixAngleMomentDirection_norm_le f z _).trans hM
  have hd : ‖d‖ ≤ (M : ℝ) * (|matrixAngleCutoff κ z| * ‖v‖ * ‖a - b‖) := by
    exact ((matrixAngleMomentDirection_lipschitzWith f z M hM).norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (matrixAngleAnsatz_sub_le f κ T z a b) M.coe_nonneg)
  have he : matrixAngleMomentCoefficientDerivative f κ T z a -
      matrixAngleMomentCoefficientDerivative f κ T z b =
      matrixAngleCutoff κ z • (ContinuousLinearMap.toSpanSingleton ℝ d).comp
        (InnerProductSpace.toDual ℝ MatrixAngleCoefficients v) := by
    ext w
    simp [matrixAngleMomentCoefficientDerivative, v, d, smul_sub]
  rw [he, norm_smul, Real.norm_eq_abs]
  calc
    |matrixAngleCutoff κ z| * ‖(ContinuousLinearMap.toSpanSingleton ℝ d).comp
        (InnerProductSpace.toDual ℝ MatrixAngleCoefficients v)‖
      ≤ |matrixAngleCutoff κ z| * (‖d‖ * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa only [ContinuousLinearMap.norm_toSpanSingleton,
          LinearIsometryEquiv.norm_map] using ContinuousLinearMap.opNorm_comp_le
            (ContinuousLinearMap.toSpanSingleton ℝ d)
            (InnerProductSpace.toDual ℝ MatrixAngleCoefficients v)
    _ ≤ |matrixAngleCutoff κ z| *
        (((M : ℝ) * (|matrixAngleCutoff κ z| * ‖v‖ * ‖a - b‖)) * ‖v‖) := by
      gcongr
    _ ≤ (R : ℝ) * (((M : ℝ) * ((R : ℝ) * (M : ℝ) * ‖a - b‖)) * (M : ℝ)) := by
      gcongr
    _ = ((R : ℝ) ^ 2 * (M : ℝ) ^ 3) * ‖a - b‖ := by ring

variable [Fact (0 < C)]

/-- The actual derivative integrand is continuous along the actual compact orbit. -/
theorem matrixAngleMomentCoefficientDerivative_continuous
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (T : ℝ) (a : MatrixAngleCoefficients) :
    Continuous (fun z ↦ matrixAngleMomentCoefficientDerivative f κ T z a) := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hb := (matrix_planar_data_contMDiff f hf).2.2.1
  have hθ : Continuous (fun z ↦ matrixAngleAnsatz f κ T a z) :=
    ((matrixAngleAnsatz_contMDiff f hf κ hκ T).comp
      (contMDiff_id.prodMk contMDiff_const)).continuous
  have hpair : Continuous (fun z ↦ (matrixAngleAnsatz f κ T a z, z)) :=
    hθ.prodMk continuous_id
  have hdir : Continuous (fun z ↦
      matrixAngleMomentDirection f (matrixAngleAnsatz f κ T a z) z) := by
    have h := (matrixAngleMomentDirection_continuous f hv.continuous hb.continuous).comp hpair
    simpa only [Function.comp_def] using h
  have hbase := (matrixAngleBaseProfile_contMDiff f hf T).continuous
  have hρ : Continuous (matrixAngleCutoff κ) :=
    ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).contMDiff.comp
      (hκ.pow 2)).continuous
  exact hρ.smul
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ MatrixAngleCoefficients).continuous.comp hdir).clm_comp ((InnerProductSpace.toDual ℝ MatrixAngleCoefficients).continuous.comp hbase))

/-- The actual first coefficient derivative is the literal average of its actual integrand. -/
theorem matrixAngleMomentMap_fderiv
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients) :
    fderiv ℝ (matrixAngleMomentMap f κ T z) a =
      orbitAverage planarHopfFlow
        (fun w ↦ matrixAngleMomentCoefficientDerivative f κ T w a) z := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  exact (matrixAngleMomentMap_hasFDerivAt f κ hv.continuous
    (matrix_planar_data_contMDiff f hf).2.2.1.continuous hκ.continuous T z a).fderiv

/-- Actual uniform fixed-amplitude bounds give an actual uniform coefficient Hessian bound. -/
theorem matrixAngleMomentMap_hessian_le_of_bounds
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (M R : ℝ≥0) (hM : ∀ z, matrixAngleAmplitude f z ≤ M)
    (hR : ∀ z, |matrixAngleCutoff κ z| ≤ R)
    (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients) :
    ‖fderiv ℝ (fderiv ℝ (matrixAngleMomentMap f κ T z)) a‖ ≤
      (R : ℝ) ^ 2 * (M : ℝ) ^ 3 := by
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hi (b : MatrixAngleCoefficients) : IntervalIntegrable
      (fun t : ℝ ↦ matrixAngleMomentCoefficientDerivative f κ T (planarHopfFlow t z) b)
      volume 0 1 :=
    ((matrixAngleMomentCoefficientDerivative_continuous f hf κ hκ T b).comp hflow).intervalIntegrable 0 1
  have hlip : LipschitzWith (R ^ 2 * M ^ 3)
      (fderiv ℝ (matrixAngleMomentMap f κ T z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro b c
    rw [dist_eq_norm, dist_eq_norm, matrixAngleMomentMap_fderiv f hf κ hκ,
      matrixAngleMomentMap_fderiv f hf κ hκ]
    change ‖(∫ t in (0 : ℝ)..1,
        matrixAngleMomentCoefficientDerivative f κ T (planarHopfFlow t z) b) -
      (∫ t in (0 : ℝ)..1,
        matrixAngleMomentCoefficientDerivative f κ T (planarHopfFlow t z) c)‖ ≤ _
    rw [← intervalIntegral.integral_sub (hi b) (hi c)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun t _ ↦
        matrixAngleMomentCoefficientDerivative_sub_le f κ T (planarHopfFlow t z)
          M R (hM _) (hR _) b c)
    simpa only [sub_zero, abs_one, mul_one, NNReal.coe_mul, NNReal.coe_pow] using h
  exact norm_fderiv_le_of_lipschitz ℝ hlip

/-- The fixed actual amplitude is continuous, with no frequency or coefficient parameter. -/
theorem matrixAngleAmplitude_continuous (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    Continuous (matrixAngleAmplitude f) := by
  obtain ⟨hs, ht, hb, _⟩ := matrix_planar_data_contMDiff f hf
  exact ((continuous_const.add ht.continuous.abs).add hs.continuous.abs).add hb.continuous.abs

/-- Compactness gives a genuine uniform Hessian bound for the literal four-moment equation,
simultaneously for every real frequency, every base point, and every coefficient. -/
theorem matrixAngleMomentMap_uniform_hessian
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients),
      ‖fderiv ℝ (fderiv ℝ (matrixAngleMomentMap f κ T z)) a‖ ≤ K := by
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    |>.exists_bound_of_continuousOn (matrixAngleAmplitude_continuous f hf).continuousOn
  have hρ : Continuous (matrixAngleCutoff κ) :=
    ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).contMDiff.comp
      (hκ.pow 2)).continuous
  obtain ⟨R, hR⟩ := (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    |>.exists_bound_of_continuousOn hρ.continuousOn
  let m : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  let r : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  have hm (z : PlanarHopfSphere C) : matrixAngleAmplitude f z ≤ m :=
    (le_abs_self _).trans ((hM z (mem_univ z)).trans (le_max_left _ _))
  have hr (z : PlanarHopfSphere C) : |matrixAngleCutoff κ z| ≤ r :=
    (hR z (mem_univ z)).trans (le_max_left _ _)
  refine ⟨(r : ℝ) ^ 2 * (m : ℝ) ^ 3, by positivity, ?_⟩
  exact fun T z a ↦ matrixAngleMomentMap_hessian_le_of_bounds f hf κ hκ m r hm hr T z a

/-- The actual native planar selector and its actual curvature have a uniform coefficient
Hessian bound; there is no separate supplied curvature or Hessian hypothesis. -/
theorem matrixAngleMomentMap_native_uniform_hessian
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients),
      ‖fderiv ℝ
        (fderiv ℝ (matrixAngleMomentMap f (planarOrbitCurvature planarHopfFlow f) T z)) a‖ ≤ K := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  exact matrixAngleMomentMap_uniform_hessian f hf _
    (planarOrbitCurvature_contMDiff planarHopfFlow f hv ha)

end GlobalEmbedding.Paper
