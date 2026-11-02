import GlobalEmbedding.Paper.MatrixAngleAnsatz
import GlobalEmbedding.Paper.MatrixNativePlanarProfiles
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Actual coefficient calculus for the four-moment angle

Source: `main.tex`, `prop:matrix`, lines299–323.
DAG node: `matrix-angle-moment-calculus`; exclusive owner W2.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Set Filter MeasureTheory Metric
open scoped Topology

namespace GlobalEmbedding.Paper

variable {C : ℕ}

/-- The actual coefficient derivative of the literal affine angle. -/
theorem matrixAngleAnsatz_hasFDerivAt (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (a : MatrixAngleCoefficients) :
    HasFDerivAt (fun a ↦ matrixAngleAnsatz f κ T a z)
      (matrixAngleCutoff κ z •
        InnerProductSpace.toDual ℝ MatrixAngleCoefficients (matrixAngleBaseProfile f T z)) a := by
  simpa [matrixAngleAnsatz] using
    ((InnerProductSpace.toDual ℝ MatrixAngleCoefficients (matrixAngleBaseProfile f T z)).hasFDerivAt.const_mul (matrixAngleCutoff κ z)).const_add
        (T * orbitDeriv planarHopfFlow f z 1)

/-- The actual coefficient derivative of the four integrands, at any coefficient. -/
theorem matrixAngleMomentIntegrand_hasFDerivAt (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (a : MatrixAngleCoefficients) :
    HasFDerivAt (fun a ↦ matrixAngleMomentValues f (matrixAngleAnsatz f κ T a z) z)
      (matrixAngleCutoff κ z •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixAngleMomentDirection f (matrixAngleAnsatz f κ T a z) z)).comp
            (InnerProductSpace.toDual ℝ MatrixAngleCoefficients
              (matrixAngleBaseProfile f T z))) a := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_smul] using
    (matrixAngleMomentValues_hasDerivAt f z (matrixAngleAnsatz f κ T a z)).hasFDerivAt.comp
      a (matrixAngleAnsatz_hasFDerivAt f κ T z a)

/-- At zero coefficient the actual coefficient derivative is precisely the Gram integrand. -/
theorem matrixAngleMomentIntegrand_zero_hasFDerivAt (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C) :
    HasFDerivAt (fun a ↦ matrixAngleMomentValues f (matrixAngleAnsatz f κ T a z) z)
      (matrixAngleCutoff κ z •
        (ContinuousLinearMap.toSpanSingleton ℝ (matrixAngleBaseProfile f T z)).comp
          (InnerProductSpace.toDual ℝ MatrixAngleCoefficients
            (matrixAngleBaseProfile f T z))) 0 := by
  simpa [matrixAngleBaseProfile] using
    matrixAngleMomentIntegrand_hasFDerivAt f κ T z 0

/-- A second angle derivative gives minus the original moment values, at every angle. -/
theorem matrixAngleMomentDirection_hasDerivAt (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) (θ : ℝ) :
    HasDerivAt (fun q : ℝ ↦ matrixAngleMomentDirection f q z)
      (-matrixAngleMomentValues f θ z) θ := by
  have h : HasDerivAt
      (fun q : ℝ ↦ ![-Real.sin q, orbitDeriv planarHopfFlow f z 1 * Real.cos q,
        -(orbitDeriv planarHopfFlow f z 0) * Real.sin q,
        matrixAngleNormalPosition f z * Real.cos q])
      ![-Real.cos θ, -(orbitDeriv planarHopfFlow f z 1 * Real.sin θ),
        -(orbitDeriv planarHopfFlow f z 0 * Real.cos θ),
        -(matrixAngleNormalPosition f z * Real.sin θ)] θ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (Real.hasDerivAt_sin θ).const_mul (-1)
    · simpa using (Real.hasDerivAt_cos θ).const_mul (orbitDeriv planarHopfFlow f z 1)
    · convert (Real.hasDerivAt_sin θ).const_mul (-(orbitDeriv planarHopfFlow f z 0)) using 1 <;> simp
    · simpa using (Real.hasDerivAt_cos θ).const_mul (matrixAngleNormalPosition f z)
  have hv := (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt θ h
  convert hv using 1
  · rfl
  · ext i
    fin_cases i <;> simp [matrixAngleMomentValues]

/-- Continuity of the literal four values, allowing the scalar angle to vary independently. -/
theorem matrixAngleMomentValues_continuous (f : PlanarHopfSphere C → Planar)
    (hv : Continuous (orbitDeriv planarHopfFlow f))
    (hb : Continuous (matrixAngleNormalPosition f)) :
    Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixAngleMomentValues f p.1 p.2) := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  have h0 : Continuous (fun p : ℝ × PlanarHopfSphere C ↦ orbitDeriv planarHopfFlow f p.2 0) := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous.comp hv).comp continuous_snd
  have h1 : Continuous (fun p : ℝ × PlanarHopfSphere C ↦ orbitDeriv planarHopfFlow f p.2 1) := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous.comp hv).comp continuous_snd
  fin_cases i
  · exact (Real.continuous_cos.comp continuous_fst)
  · exact h1.mul (Real.continuous_sin.comp continuous_fst)
  · exact h0.mul (Real.continuous_cos.comp continuous_fst)
  · exact (hb.comp continuous_snd).mul (Real.continuous_sin.comp continuous_fst)

/-- Continuity of the literal angle derivative profile jointly in angle and point. -/
theorem matrixAngleMomentDirection_continuous (f : PlanarHopfSphere C → Planar)
    (hv : Continuous (orbitDeriv planarHopfFlow f))
    (hb : Continuous (matrixAngleNormalPosition f)) :
    Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixAngleMomentDirection f p.1 p.2) := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  have h0 : Continuous (fun p : ℝ × PlanarHopfSphere C ↦ orbitDeriv planarHopfFlow f p.2 0) := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous.comp hv).comp continuous_snd
  have h1 : Continuous (fun p : ℝ × PlanarHopfSphere C ↦ orbitDeriv planarHopfFlow f p.2 1) := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous.comp hv).comp continuous_snd
  fin_cases i
  · exact (Real.continuous_sin.comp continuous_fst).neg
  · exact h1.mul (Real.continuous_cos.comp continuous_fst)
  · exact h0.neg.mul (Real.continuous_sin.comp continuous_fst)
  · exact (hb.comp continuous_snd).mul (Real.continuous_cos.comp continuous_fst)

/-- Compact-period differentiation with the actual continuously varying derivative.
The compact coefficient ball supplies the domination, so no derivative bound is assumed. -/
private theorem hasFDerivAt_compact_period
    (F : MatrixAngleCoefficients × ℝ → MatrixAngleCoefficients)
    (L : MatrixAngleCoefficients × ℝ → MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients)
    (hF : Continuous F) (hL : Continuous L)
    (hd : ∀ a t, HasFDerivAt (fun a ↦ F (a, t)) (L (a, t)) a)
    (a : MatrixAngleCoefficients) :
    HasFDerivAt (fun a ↦ ∫ t in Icc (0 : ℝ) 1, F (a, t))
      (∫ t in Icc (0 : ℝ) 1, L (a, t)) a := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall a (1 : ℝ)).prod isCompact_Icc).exists_bound_of_continuousOn hL.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (s := ball a 1) (bound := fun _ ↦ B) (ball_mem_nhds a zero_lt_one)
  · exact .of_forall fun q ↦
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.aestronglyMeasurable
        measurableSet_Icc
  · exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
  · exact (hL.comp (continuous_const.prodMk continuous_id)).continuousOn.aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht q hq
    exact hB (q, t) ⟨ball_subset_closedBall hq, ht⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · exact .of_forall fun t q _ ↦ hd q t

/-- The actual averaged coefficient derivative, justified by compact-period domination. -/
theorem matrixAngleMomentMap_hasFDerivAt [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (hv : Continuous (orbitDeriv planarHopfFlow f))
    (hb : Continuous (matrixAngleNormalPosition f)) (hκ : Continuous κ)
    (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients) :
    HasFDerivAt (matrixAngleMomentMap f κ T z)
      (orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixAngleMomentDirection f (matrixAngleAnsatz f κ T a w) w)).comp
            (InnerProductSpace.toDual ℝ MatrixAngleCoefficients
              (matrixAngleBaseProfile f T w))) z) a := by
  have hphase : Continuous (fun w ↦ T * orbitDeriv planarHopfFlow f w 1) :=
    continuous_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous.comp hv)
  have hbase : Continuous (matrixAngleBaseProfile f T) := by
    have hp : Continuous (fun w : PlanarHopfSphere C ↦
        (T * orbitDeriv planarHopfFlow f w 1, w)) := hphase.prodMk continuous_id
    change Continuous (fun w ↦ matrixAngleBaseProfile f T w)
    have h := (matrixAngleMomentDirection_continuous f hv hb).comp hp
    simpa only [matrixAngleBaseProfile, Function.comp_def] using h
  have hρ : Continuous (matrixAngleCutoff κ) := (expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp (hκ.pow 2)
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have hw : Continuous (fun p : MatrixAngleCoefficients × ℝ ↦ planarHopfFlow p.2 z) :=
    hflow.comp continuous_snd
  have hθ : Continuous (fun p : MatrixAngleCoefficients × ℝ ↦
      matrixAngleAnsatz f κ T p.1 (planarHopfFlow p.2 z)) :=
    (hphase.comp hw).add ((hρ.comp hw).mul ((hbase.comp hw).inner continuous_fst))
  let F : MatrixAngleCoefficients × ℝ → MatrixAngleCoefficients := fun p ↦
    matrixAngleMomentValues f (matrixAngleAnsatz f κ T p.1 (planarHopfFlow p.2 z))
      (planarHopfFlow p.2 z)
  let L : MatrixAngleCoefficients × ℝ → MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients :=
    fun p ↦ matrixAngleCutoff κ (planarHopfFlow p.2 z) •
      (ContinuousLinearMap.toSpanSingleton ℝ
        (matrixAngleMomentDirection f (matrixAngleAnsatz f κ T p.1 (planarHopfFlow p.2 z))
          (planarHopfFlow p.2 z))).comp
        (InnerProductSpace.toDual ℝ MatrixAngleCoefficients
          (matrixAngleBaseProfile f T (planarHopfFlow p.2 z)))
  have hF : Continuous F := by
    have hp : Continuous (fun p : MatrixAngleCoefficients × ℝ ↦
        (matrixAngleAnsatz f κ T p.1 (planarHopfFlow p.2 z), planarHopfFlow p.2 z)) :=
      hθ.prodMk hw
    have h := (matrixAngleMomentValues_continuous f hv hb).comp hp
    change Continuous (fun p ↦ F p)
    simpa only [F, Function.comp_def] using h
  have hL : Continuous L :=
    (hρ.comp hw).smul
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ MatrixAngleCoefficients).continuous.comp
        ((matrixAngleMomentDirection_continuous f hv hb).comp (hθ.prodMk hw))).clm_comp
          ((InnerProductSpace.toDual ℝ MatrixAngleCoefficients).continuous.comp (hbase.comp hw)))
  have h := hasFDerivAt_compact_period F L hF hL
    (fun q t ↦ matrixAngleMomentIntegrand_hasFDerivAt f κ T (planarHopfFlow t z) q) a
  change HasFDerivAt (fun q ↦ matrixAngleMomentMap f κ T z q) _ a
  simpa only [F, L, matrixAngleMomentMap, orbitAverage,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] using h

/-- The actual derivative at zero equals the literal weighted Gram operator. -/
theorem matrixAngleMomentMap_zero_hasFDerivAt [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (hv : Continuous (orbitDeriv planarHopfFlow f))
    (hb : Continuous (matrixAngleNormalPosition f)) (hκ : Continuous κ)
    (T : ℝ) (z : PlanarHopfSphere C) :
    HasFDerivAt (matrixAngleMomentMap f κ T z) (matrixAngleGram f κ T z) 0 := by
  simpa only [matrixAngleAnsatz_zero, matrixAngleBaseProfile, matrixAngleGram] using
    matrixAngleMomentMap_hasFDerivAt f κ hv hb hκ T z 0

/-- The actual Frechet derivative of the averaged moment equation at zero. -/
theorem matrixAngleMomentMap_fderiv_zero [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (hv : Continuous (orbitDeriv planarHopfFlow f))
    (hb : Continuous (matrixAngleNormalPosition f)) (hκ : Continuous κ)
    (T : ℝ) (z : PlanarHopfSphere C) :
    fderiv ℝ (matrixAngleMomentMap f κ T z) 0 = matrixAngleGram f κ T z :=
  (matrixAngleMomentMap_zero_hasFDerivAt f κ hv hb hκ T z).fderiv

/-- The derivative identity for the actual native smooth planar map and its actual curvature;
all continuity premises of the compact-period calculation are discharged here. -/
theorem matrixAngleMomentMap_native_fderiv_zero [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (T : ℝ) (z : PlanarHopfSphere C) :
    fderiv ℝ (matrixAngleMomentMap f (planarOrbitCurvature planarHopfFlow f) T z) 0 =
      matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  exact matrixAngleMomentMap_fderiv_zero f (planarOrbitCurvature planarHopfFlow f)
    hv.continuous (matrix_planar_data_contMDiff f hf).2.2.1.continuous
    (planarOrbitCurvature_contMDiff planarHopfFlow f hv ha).continuous T z

end GlobalEmbedding.Paper
