import GlobalEmbedding.Paper.MatrixNativePlanarProfiles

/-!
# Actual finite-amplitude oscillation and the four original residuals

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, lines293–313.
DAG: `matrix-native-angle-residual`.
The actual shared Euclidean coefficient space, moment map and Gram operator are used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- One common frequency threshold works for any finite collection of actual smooth
amplitudes, positive frequency multiples and real phase shifts on the actual Hopf sphere.

Proof: the preceding actual Hopf oscillatory theorem applies to each amplitude. Pull
its actual atTop filter back by multiplication by the fixed positive frequency factor.
A finite filter intersection gives a common threshold over every amplitude and the whole
sphere. Source: prop:matrix, finite amplitudes and T/2T, line293. -/
theorem matrix_hopf_finite_oscillatory_average
    {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    {ι : Type*} [Fintype ι] (a : ι → PlanarHopfSphere C → ℝ)
    (ha : ∀ i, ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (a i))
    (ν phase : ι → ℝ) (hν : ∀ i, 0 < ν i) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ i z,
      |orbitAverage planarHopfFlow
        (fun w ↦ a i w * Real.cos ((ν i * T) * matrixPlanarT f w + phase i)) z| < ε := by
  have hconv (i : ι) : TendstoUniformly
      (fun T : ℝ ↦ orbitAverage planarHopfFlow
        (fun w ↦ a i w * Real.cos ((ν i * T) * matrixPlanarT f w + phase i)))
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
    intro V hV
    exact (tendsto_id.const_mul_atTop (hν i))
      ((matrix_hopf_uniform_oscillatory_average f hf hunit hana (a i) (ha i) (phase i)) V hV)
  have hsmall (i : ι) : ∀ᶠ T : ℝ in atTop, ∀ z,
      |orbitAverage planarHopfFlow
        (fun w ↦ a i w * Real.cos ((ν i * T) * matrixPlanarT f w + phase i)) z| < ε := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using
      (Metric.tendstoUniformly_iff.mp (hconv i)) ε hε
  exact Filter.eventually_all.mpr hsmall

/-- The literal four residual moments at coefficient zero tend uniformly to zero on the
whole actual Hopf sphere, in the original Euclidean coefficient norm.

Proof: use the preceding finite-amplitude theorem for amplitudes 1,t,s,b and the phase
shifts 0,-pi/2,0,-pi/2. Actual coordinate projections commute with the integrable actual
moment integral. The four scalar uniform bounds give the actual Euclidean norm bound by
the sum-of-squares formula. Source: prop:matrix, four small residuals, lines303–311. -/
theorem matrix_angle_residual_tendsto_uniformly
    {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (κ : PlanarHopfSphere C → ℝ) :
    TendstoUniformly (fun T : ℝ ↦ fun z ↦ matrixAngleMomentMap f κ T z 0)
      (fun _ : PlanarHopfSphere C ↦ (0 : MatrixAngleCoefficients)) atTop := by
  obtain ⟨hs, ht, hb, _⟩ := matrix_planar_data_contMDiff f hf
  let a : Fin 4 → PlanarHopfSphere C → ℝ := ![fun _ ↦ 1,
    matrixPlanarT f, matrixPlanarS f, matrixPlanarB f]
  let phase : Fin 4 → ℝ := ![0, -(Real.pi / 2), 0, -(Real.pi / 2)]
  have ha (i : Fin 4) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (a i) := by
    fin_cases i
    · exact contMDiff_const
    · exact ht
    · exact hs
    · exact hb
  have hentry (T : ℝ) (z : PlanarHopfSphere C) (i : Fin 4) :
      matrixAngleMomentMap f κ T z 0 i = orbitAverage planarHopfFlow
        (fun w ↦ a i w * Real.cos (T * matrixPlanarT f w + phase i)) z := by
    have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have ht' := ht.continuous.comp hflow
    have hs' := hs.continuous.comp hflow
    have hb' := hb.continuous.comp hflow
    have hc : Continuous (fun t : ℝ ↦ matrixAngleMomentValues f
        (T * matrixPlanarT f (planarHopfFlow t z)) (planarHopfFlow t z)) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp
      apply continuous_pi
      intro j
      fin_cases j
      · exact (Real.continuous_cos.comp (continuous_const.mul ht'))
      · exact ht'.mul (Real.continuous_sin.comp (continuous_const.mul ht'))
      · exact hs'.mul (Real.continuous_cos.comp (continuous_const.mul ht'))
      · exact hb'.mul (Real.continuous_sin.comp (continuous_const.mul ht'))
    change (∫ t in (0 : ℝ)..1,
      matrixAngleMomentValues f (matrixAngleAnsatz f κ T 0 (planarHopfFlow t z))
        (planarHopfFlow t z)) i = _
    simp only [matrixAngleAnsatz_zero]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    change (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) i)
      (∫ t in Icc (0 : ℝ) 1, matrixAngleMomentValues f
        (T * matrixPlanarT f (planarHopfFlow t z)) (planarHopfFlow t z)) = _
    rw [← (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) i).integral_comp_comm
      hc.continuousOn.integrableOn_Icc]
    change (∫ t in Icc (0 : ℝ) 1,
      matrixAngleMomentValues f (T * matrixPlanarT f (planarHopfFlow t z))
        (planarHopfFlow t z) i) = _
    change _ = ∫ t in (0 : ℝ)..1,
      a i (planarHopfFlow t z) *
        Real.cos (T * matrixPlanarT f (planarHopfFlow t z) + phase i)
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards with t
    fin_cases i <;>
      simp [matrixAngleMomentValues, a, phase, matrixPlanarT, matrixPlanarS,
        matrixPlanarB, ← sub_eq_add_neg, Real.cos_sub_pi_div_two]
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hδ : 0 < ε / 3 := by positivity
  have hsmall := matrix_hopf_finite_oscillatory_average f hf hunit hana a ha
    (fun _ ↦ 1) phase (fun _ ↦ zero_lt_one) (ε / 3) hδ
  filter_upwards [hsmall] with T hT z
  let v := matrixAngleMomentMap f κ T z 0
  have hv (i : Fin 4) : |v i| < ε / 3 := by
    simpa only [v, hentry, one_mul] using hT i z
  have hn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq v
  have hsquare (i : Fin 4) : v i ^ 2 < (ε / 3) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) hδ.le).mpr (hv i)
  have hnorm : ‖v‖ < ε := by
    nlinarith [hsquare 0, hsquare 1, hsquare 2, hsquare 3, norm_nonneg v]
  simpa only [dist_zero_left, norm_neg] using hnorm

#print axioms matrix_hopf_finite_oscillatory_average
#print axioms matrix_angle_residual_tendsto_uniformly

end GlobalEmbedding.Paper
