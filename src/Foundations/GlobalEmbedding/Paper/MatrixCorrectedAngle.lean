import GlobalEmbedding.Paper.MatrixAngleNativeSmoothFlat
import GlobalEmbedding.Paper.MatrixAngleCoefficientRoot
import GlobalEmbedding.Paper.MatrixAngleOrbitError

/-!
# The actual corrected angle for the original matrix proof

Source: `main.tex`, `prop:matrix`, lines307–323.
DAG node: `matrix-corrected-angle`; exclusive owner W2.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open Set

namespace GlobalEmbedding.Paper

variable {C : ℕ} [Fact (0 < C)]

/-- The actual curvature cutoff has zero actual orbit derivative on curvature zero. -/
theorem matrixAngleCutoff_hasDerivAt_zero
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (z : PlanarHopfSphere C) (hz : κ z = 0) :
    HasDerivAt (fun s : ℝ ↦ matrixAngleCutoff κ (planarHopfFlow s z)) 0 0 := by
  have hk : HasDerivAt (fun s : ℝ ↦ κ (planarHopfFlow s z))
      (orbitDeriv planarHopfFlow κ z) 0 := by
    simpa only [planarHopfFlow_zero] using
      hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C) planarHopfFlow_add κ hκ 0 z
  have hs : HasDerivAt (fun s : ℝ ↦ κ (planarHopfFlow s z) ^ 2) 0 0 := by
    simpa only [Pi.pow_apply, planarHopfFlow_zero, hz, zero_pow (by decide : 1 ≠ 0), mul_zero, zero_mul] using hk.fun_pow 2
  have hd := ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).differentiable (by simp) (κ (planarHopfFlow 0 z) ^ 2)).hasDerivAt.comp 0 hs
  simpa only [matrixAngleCutoff, Function.comp_def, mul_zero] using hd

/-- At curvature zero, every actual smooth ansatz correction has zero orbit derivative.
The remaining angle derivative is exactly T times the actual phase derivative. -/
theorem matrixAngleAnsatz_orbitDeriv_at_zero
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ c)
    (z : PlanarHopfSphere C) (hz : κ z = 0) :
    orbitDeriv planarHopfFlow (fun w ↦ matrixAngleAnsatz f κ T (c w) w) z =
      T * orbitDeriv planarHopfFlow (fun w ↦ orbitDeriv planarHopfFlow f w 1) z := by
  let g : PlanarHopfSphere C → ℝ := fun w ↦ ⟪matrixAngleBaseProfile f T w, c w⟫
  have hg : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ g :=
    (contDiff_inner : ContDiff ℝ ∞
      (fun p : MatrixAngleCoefficients × MatrixAngleCoefficients ↦ ⟪p.1, p.2⟫)).contMDiff.comp
        ((matrixAngleBaseProfile_contMDiff f hf T).prodMk_space hc)
  have hgd := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add g hg 0 z
  have hcor := (matrixAngleCutoff_hasDerivAt_zero κ hκ z hz).fun_mul hgd
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have htd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add (matrixPlanarT f) ht 0 z).const_mul T
  have h := htd.fun_add hcor
  have he : matrixAngleCutoff κ z = 0 := by simp [matrixAngleCutoff, hz]
  simpa only [orbitDeriv, matrixAngleAnsatz, g, matrixPlanarT, planarHopfFlow_zero,
    he, zero_mul, mul_zero, add_zero, Pi.add_apply, Pi.mul_apply] using h.deriv

/-- The actual native curvature is antipodally odd for the actual reflected planar map. -/
theorem matrixAngleNativeCurvature_odd
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hreflect : ∀ z, f (-z) = planarReflection (f z)) (z : PlanarHopfSphere C) :
    planarOrbitCurvature planarHopfFlow f (-z) = -planarOrbitCurvature planarHopfFlow f z := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hfd (w : PlanarHopfSphere C) : Differentiable ℝ (fun s ↦ f (planarHopfFlow s w)) :=
    fun s ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf s w).differentiableAt
  have hvd (w : PlanarHopfSphere C) :
      Differentiable ℝ (fun s ↦ orbitDeriv planarHopfFlow f (planarHopfFlow s w)) :=
    fun s ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv s w).differentiableAt
  have hhalf (w : PlanarHopfSphere C) :
      f (planarHopfFlow (1 / 2) w) = planarReflection (f w) := by
    simpa only [planarHopfFlow_half] using hreflect w
  simpa only [planarHopfFlow_half] using
    planarOrbitCurvature_half_odd planarHopfFlow planarHopfFlow_add
      planarHopfFlow_zero f hfd hvd hhalf z

/-- Actual unit speed forces the actual phase derivative Xt to vanish on actual curvature zero. -/
theorem matrixAngleNativePhase_orbitDeriv_zero
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (z : PlanarHopfSphere C) (hz : planarOrbitCurvature planarHopfFlow f z = 0) :
    orbitDeriv planarHopfFlow (fun w ↦ orbitDeriv planarHopfFlow f w 1) z = 0 := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hfd (w : PlanarHopfSphere C) : Differentiable ℝ (fun s ↦ f (planarHopfFlow s w)) :=
    fun s ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf s w).differentiableAt
  have hvd (w : PlanarHopfSphere C) :
      Differentiable ℝ (fun s ↦ orbitDeriv planarHopfFlow f (planarHopfFlow s w)) :=
    fun s ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv s w).differentiableAt
  have hacc := planarOrbitCurvature_acceleration planarHopfFlow planarHopfFlow_add
    planarHopfFlow_zero f hfd hvd hunit z
  have he : orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z 1 = 0 := by
    simpa only [hz, zero_smul, PiLp.zero_apply] using congrArg (fun v : Planar ↦ v 1) hacc
  have hd := (planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add
    (orbitDeriv planarHopfFlow f) hvd z 0 1).deriv
  have heq : orbitDeriv planarHopfFlow (fun w ↦ orbitDeriv planarHopfFlow f w 1) z =
      orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow f) z 1 := by
    simpa only [orbitDeriv, planarHopfFlow_zero] using hd
  exact heq.trans he

/-- The actual corrected ansatz angle has Xtheta=0 on actual curvature zero.
Every native smooth coefficient field is allowed here, including the actual small roots. -/
theorem matrixAngleAnsatz_native_orbitDeriv_zero
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1) (T : ℝ)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ c)
    (z : PlanarHopfSphere C) (hz : planarOrbitCurvature planarHopfFlow f z = 0) :
    orbitDeriv planarHopfFlow
      (fun w ↦ matrixAngleAnsatz f (planarOrbitCurvature planarHopfFlow f) T (c w) w) z = 0 := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  rw [matrixAngleAnsatz_orbitDeriv_at_zero f hf _
    (planarOrbitCurvature_contMDiff planarHopfFlow f hv ha) T c hc z hz,
    matrixAngleNativePhase_orbitDeriv_zero f hf hunit z hz, mul_zero]

/-- The actual vector moment equation gives exactly the four original scalar orbit equations. -/
theorem matrixAngle_four_moments_of_vector_zero
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (θ : PlanarHopfSphere C → ℝ)
    (hθ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ θ)
    (z : PlanarHopfSphere C)
    (hzero : orbitAverage planarHopfFlow (fun w ↦ matrixAngleMomentValues f (θ w) w) z = 0) :
    orbitAverage planarHopfFlow (fun w ↦ Real.cos (θ w)) z = 0 ∧
      orbitAverage planarHopfFlow
        (fun w ↦ orbitDeriv planarHopfFlow f w 1 * Real.sin (θ w)) z = 0 ∧
      orbitAverage planarHopfFlow
        (fun w ↦ orbitDeriv planarHopfFlow f w 0 * Real.cos (θ w)) z = 0 ∧
      orbitAverage planarHopfFlow
        (fun w ↦ matrixAngleNormalPosition f w * Real.sin (θ w)) z = 0 := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hb := (matrix_planar_data_contMDiff f hf).2.2.1
  have hp : Continuous (fun w ↦ (θ w, w)) := hθ.continuous.prodMk continuous_id
  have hV := (matrixAngleMomentValues_continuous f hv.continuous hb.continuous).comp hp
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hi := (hV.comp hflow).intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1
  have hcoord (i : Fin 4) : orbitAverage planarHopfFlow
      (fun w ↦ matrixAngleMomentValues f (θ w) w i) z = 0 := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) i).intervalIntegral_comp_comm hi
    change orbitAverage planarHopfFlow (fun w ↦ matrixAngleMomentValues f (θ w) w i) z =
      (orbitAverage planarHopfFlow (fun w ↦ matrixAngleMomentValues f (θ w) w) z) i at h
    simpa only [hzero, PiLp.zero_apply] using h
  exact ⟨hcoord 0, hcoord 1, hcoord 2, hcoord 3⟩

omit [Fact (0 < C)] in
/-- The combined uniform pointwise estimate implies exactly the sum of the two
compact C0 norms occurring in the original equation (3.3). Each norm is bounded
by the common pointwise error bound, and the two bounds are added. -/
theorem matrixAngle_norm_error_tendsto_of_uniform
    (e d : ℝ → C(PlanarHopfSphere C, ℝ))
    (h : TendstoUniformly (fun T z ↦ |e T z| + T⁻¹ * |d T z|)
      (fun _ ↦ (0 : ℝ)) Filter.atTop) :
    Filter.Tendsto (fun T ↦ ‖e T‖ + T⁻¹ * ‖d T‖) Filter.atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hq : 0 < ε / 4 := by positivity
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) (ε / 4) hq,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hT hlarge
  have hi : 0 ≤ T⁻¹ := inv_nonneg.mpr (by linarith)
  have hb (z : PlanarHopfSphere C) : |e T z| + T⁻¹ * |d T z| < ε / 4 := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hi (abs_nonneg _)))] using hT z
  have he : ‖e T‖ ≤ ε / 4 := (ContinuousMap.norm_le _ hq.le).mpr fun z ↦ by
    rw [Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (mul_nonneg hi (abs_nonneg _))).trans (hb z).le
  have hd : ‖T⁻¹ • d T‖ ≤ ε / 4 := (ContinuousMap.norm_le _ hq.le).mpr fun z ↦ by
    change ‖T⁻¹ * d T z‖ ≤ ε / 4
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hi]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hb z).le
  have hd' : T⁻¹ * ‖d T‖ ≤ ε / 4 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi] using hd
  rw [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hi (norm_nonneg _)))]
  linarith

/-- The original actual corrected angle family: native smoothness, reflection oddness,
all four literal orbit moments, full native flatness, Xtheta=0 on actual curvature zero,
and the original uniform C0 plus scaled-X error. No corrected angle is assumed. -/
theorem matrixCorrectedAngleFamily_exists
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hreflect : ∀ z, f (-z) = planarReflection (f z))
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ) :
    ∃ θ : ℝ → PlanarHopfSphere C → ℝ,
      (∀ T, ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (θ T)) ∧
      (∀ T, ManifoldFlatOn (I := planarHopfModel C)
        (fun z ↦ θ T z - T * orbitDeriv planarHopfFlow f z 1)
        {z | planarOrbitCurvature planarHopfFlow f z = 0}) ∧
      (∀ T z, planarOrbitCurvature planarHopfFlow f z = 0 →
        orbitDeriv planarHopfFlow (θ T) z = 0) ∧
      (∀ᶠ T : ℝ in Filter.atTop,
        (∀ z, θ T (-z) = -θ T z) ∧
        (∀ z, orbitAverage planarHopfFlow (fun w ↦ Real.cos (θ T w)) z = 0 ∧
          orbitAverage planarHopfFlow
            (fun w ↦ orbitDeriv planarHopfFlow f w 1 * Real.sin (θ T w)) z = 0 ∧
          orbitAverage planarHopfFlow
            (fun w ↦ orbitDeriv planarHopfFlow f w 0 * Real.cos (θ T w)) z = 0 ∧
          orbitAverage planarHopfFlow
            (fun w ↦ matrixAngleNormalPosition f w * Real.sin (θ T w)) z = 0)) ∧
      TendstoUniformly
        (fun T z ↦ |θ T z - T * orbitDeriv planarHopfFlow f z 1| +
          T⁻¹ * |orbitDeriv planarHopfFlow
            (fun w ↦ θ T w - T * orbitDeriv planarHopfFlow f w 1) z|)
        (fun _ ↦ (0 : ℝ)) Filter.atTop ∧
      (∃ e d : ℝ → C(PlanarHopfSphere C, ℝ),
        (∀ T z, e T z = θ T z - T * orbitDeriv planarHopfFlow f z 1) ∧
        (∀ T z, d T z = orbitDeriv planarHopfFlow
          (fun w ↦ θ T w - T * orbitDeriv planarHopfFlow f w 1) z) ∧
        Filter.Tendsto (fun T ↦ ‖e T‖ + T⁻¹ * ‖d T‖) Filter.atTop (nhds 0)) := by
  obtain ⟨c, hc, hclim, hcdata⟩ := matrixAngleCoefficientRoot_exists f hf hunit hana
  let κ := planarOrbitCurvature planarHopfFlow f
  let θ : ℝ → PlanarHopfSphere C → ℝ := fun T z ↦ matrixAngleAnsatz f κ T (c T z) z
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  have hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ :=
    planarOrbitCurvature_contMDiff planarHopfFlow f hv ha
  have hθ (T : ℝ) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (θ T) := by
    have hp : ContMDiff (planarHopfModel C)
        ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)) ∞
        (fun z : PlanarHopfSphere C ↦ (z, c T z)) := contMDiff_id.prodMk (hc T)
    have hs := (matrixAngleAnsatz_contMDiff f hf κ hκ T).comp hp
    change ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (fun z ↦ θ T z)
    simpa only [θ, Function.comp_def] using hs
  have hlim := matrixAngleAnsatz_scaled_error_tendstoUniformly f hf κ hκ c
    (hcdata.mono fun _ hT ↦ hT.2) hclim
  refine ⟨θ, hθ, ?_, ?_, ?_, hlim, ?_⟩
  · exact fun T ↦ matrixAngleAnsatz_sub_phase_flat f hf κ hκ T (c T) (hc T)
  · exact fun T z hz ↦ matrixAngleAnsatz_native_orbitDeriv_zero f hf hunit T (c T) (hc T) z hz
  · apply hcdata.mono
    intro T hT
    refine ⟨fun z ↦ matrixAngleAnsatz_basic_odd f hf hreflect κ
      (matrixAngleNativeCurvature_odd f hf hreflect) T (c T) hT.2 z, ?_⟩
    intro z
    have hvec : orbitAverage planarHopfFlow (fun w ↦ matrixAngleMomentValues f (θ T w) w) z = 0 := by
      calc
        _ = matrixAngleMomentMap f κ T z (c T z) := by
          unfold matrixAngleMomentMap orbitAverage
          apply intervalIntegral.integral_congr
          intro s _
          change matrixAngleMomentValues f
            (matrixAngleAnsatz f κ T (c T (planarHopfFlow s z)) (planarHopfFlow s z))
            (planarHopfFlow s z) = _
          rw [hT.2 z s]
        _ = 0 := hT.1 z
    exact matrixAngle_four_moments_of_vector_zero f hf (θ T) (hθ T) z hvec
  · have he (T : ℝ) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
        (fun z ↦ θ T z - T * orbitDeriv planarHopfFlow f z 1) :=
      (hθ T).sub (contMDiff_const.mul (matrix_planar_data_contMDiff f hf).2.1)
    let e : ℝ → C(PlanarHopfSphere C, ℝ) := fun T ↦
      ⟨_, (he T).continuous⟩
    let d : ℝ → C(PlanarHopfSphere C, ℝ) := fun T ↦
      ⟨_, (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ (he T)).continuous⟩
    exact ⟨e, d, fun _ _ ↦ rfl, fun _ _ ↦ rfl,
      matrixAngle_norm_error_tendsto_of_uniform e d hlim⟩

end GlobalEmbedding.Paper
