import GlobalEmbedding.Paper.MatrixAngleAnsatz
import GlobalEmbedding.Paper.MatrixNativePlanarProfiles
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import GlobalEmbedding.Paper.MatrixManifoldFlatCurvatureCutoff
import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import GlobalEmbedding.Paper.PlanarHopfFourierReflection
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Native smoothness and flatness of the actual angle ansatz

Source: `main.tex`, `prop:matrix`, lines299–323.
DAG node: `matrix-angle-native-smooth-flat`; exclusive owner W2.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open Set MeasureTheory

namespace GlobalEmbedding.Paper

private theorem contMDiff_euclidean_four
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {g0 g1 g2 g3 : M → ℝ}
    (h0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ g0) (h1 : ContMDiff I 𝓘(ℝ, ℝ) ∞ g1)
    (h2 : ContMDiff I 𝓘(ℝ, ℝ) ∞ g2) (h3 : ContMDiff I 𝓘(ℝ, ℝ) ∞ g3) :
    ContMDiff I 𝓘(ℝ, MatrixAngleCoefficients) ∞
      (fun z ↦ WithLp.toLp 2 ![g0 z, g1 z, g2 z, g3 z]) := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

variable {C : ℕ} [Fact (0 < C)]

/-- The actual oscillatory direction profile is native smooth for every fixed frequency. -/
theorem matrixAngleBaseProfile_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) (T : ℝ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞
      (matrixAngleBaseProfile f T) := by
  obtain ⟨hs, ht, hb, _⟩ := matrix_planar_data_contMDiff f hf
  have hphase : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ T * matrixPlanarT f z) := contMDiff_const.mul ht
  have hsin := Real.contDiff_sin.contMDiff.comp (show
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ T * matrixPlanarT f z) from hphase)
  have hcos := Real.contDiff_cos.contMDiff.comp (show
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ T * matrixPlanarT f z) from hphase)
  exact contMDiff_euclidean_four hsin.neg (ht.mul hcos) (hs.neg.mul hsin) (hb.mul hcos)

/-- The actual angle is native smooth jointly in point and coefficient. -/
theorem matrixAngleAnsatz_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)) 𝓘(ℝ, ℝ) ∞
      (fun p : PlanarHopfSphere C × MatrixAngleCoefficients ↦
        matrixAngleAnsatz f κ T p.2 p.1) := by
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have hbase : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
      𝓘(ℝ, MatrixAngleCoefficients) ∞
      (fun p : PlanarHopfSphere C × MatrixAngleCoefficients ↦ matrixAngleBaseProfile f T p.1) :=
    (matrixAngleBaseProfile_contMDiff f hf T).comp contMDiff_fst
  have hρ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixAngleCutoff κ) :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  have hi := (contDiff_inner : ContDiff ℝ ∞ (fun p : MatrixAngleCoefficients × MatrixAngleCoefficients ↦ ⟪p.1, p.2⟫)).contMDiff.comp (hbase.prodMk_space contMDiff_snd)
  exact (contMDiff_const.mul (ht.comp contMDiff_fst)).add ((hρ.comp contMDiff_fst).mul hi)

/-- The literal moment integrands are native smooth jointly in point and coefficient. -/
theorem matrixAngleMomentIntegrand_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
      𝓘(ℝ, MatrixAngleCoefficients) ∞
      (fun p : PlanarHopfSphere C × MatrixAngleCoefficients ↦
        matrixAngleMomentValues f (matrixAngleAnsatz f κ T p.2 p.1) p.1) := by
  obtain ⟨hs, ht, hb, _⟩ := matrix_planar_data_contMDiff f hf
  have hθ := matrixAngleAnsatz_contMDiff f hf κ hκ T
  have hsin := Real.contDiff_sin.contMDiff.comp hθ
  have hcos := Real.contDiff_cos.contMDiff.comp hθ
  exact contMDiff_euclidean_four hcos ((ht.comp contMDiff_fst).mul hsin)
    ((hs.comp contMDiff_fst).mul hcos) ((hb.comp contMDiff_fst).mul hsin)

/-- Native full smoothness of the actual averaged four-moment map. -/
theorem matrixAngleMomentMap_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
      𝓘(ℝ, MatrixAngleCoefficients) ∞
      (Function.uncurry (matrixAngleMomentMap f κ T)) := by
  let F : (PlanarHopfSphere C × MatrixAngleCoefficients) × ℝ → MatrixAngleCoefficients :=
    fun p ↦ matrixAngleMomentValues f
      (matrixAngleAnsatz f κ T p.1.2 (planarHopfFlow p.2 p.1.1))
      (planarHopfFlow p.2 p.1.1)
  have hw : ContMDiff
      (((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)).prod 𝓘(ℝ, ℝ))
      (planarHopfModel C) ∞ (fun p : (PlanarHopfSphere C × MatrixAngleCoefficients) × ℝ ↦
        planarHopfFlow p.2 p.1.1) :=
    (planarHopfFlow_contMDiff C).comp
      (contMDiff_snd.prodMk (contMDiff_fst.comp contMDiff_fst))
  have hF : ContMDiff
      (((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, MatrixAngleCoefficients) ∞ F := by
    have hp : ContMDiff
        (((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)).prod 𝓘(ℝ, ℝ))
        ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)) ∞
        (fun p : (PlanarHopfSphere C × MatrixAngleCoefficients) × ℝ ↦
          (planarHopfFlow p.2 p.1.1, p.1.2)) :=
      hw.prodMk (contMDiff_snd.comp contMDiff_fst)
    have h := (matrixAngleMomentIntegrand_contMDiff f hf κ hκ T).comp hp
    change ContMDiff _ _ ∞ (fun p ↦ F p)
    simpa only [F, Function.comp_def] using h
  have hman : IsManifold ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients)) ∞
      (PlanarHopfSphere C × MatrixAngleCoefficients) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixAngleCoefficients)
      (PlanarHopfSphere C × MatrixAngleCoefficients) :=
    inferInstanceAs (ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin (2 * C - 1))) MatrixAngleCoefficients)
      (PlanarHopfSphere C × MatrixAngleCoefficients))
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixAngleCoefficients) ∞
      (PlanarHopfSphere C × MatrixAngleCoefficients) := by
    simpa only [modelWithCornersSelf_prod] using hman
  have h := contMDiff_compact_parameter_integral
    (P := EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixAngleCoefficients) (⊤ : ℕ∞) F
    (by simpa only [modelWithCornersSelf_prod] using hF)
  have hI : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
      𝓘(ℝ, MatrixAngleCoefficients) ∞
      (fun p : PlanarHopfSphere C × MatrixAngleCoefficients ↦ ∫ t in Icc (0 : ℝ) 1, F (p, t)) := by
    simpa only [modelWithCornersSelf_prod] using h
  apply hI.congr
  intro p
  change matrixAngleMomentMap f κ T p.1 p.2 = _
  simp only [F, matrixAngleMomentMap, orbitAverage,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]


/-- Any native smooth coefficient field gives an actual angle correction flat in every
native chart on curvature zero. No orbit-only flatness predicate is substituted. -/
theorem matrixAngleAnsatz_sub_phase_flat (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ c) :
    ManifoldFlatOn (I := planarHopfModel C)
      (fun z ↦ matrixAngleAnsatz f κ T (c z) z - T * orbitDeriv planarHopfFlow f z 1)
      {z | κ z = 0} := by
  have hi := (contDiff_inner : ContDiff ℝ ∞ (fun p : MatrixAngleCoefficients × MatrixAngleCoefficients ↦ ⟪p.1, p.2⟫)).contMDiff.comp
    ((matrixAngleBaseProfile_contMDiff f hf T).prodMk_space hc)
  have h := manifold_flat_curvature_cutoff_smul κ hκ
    (fun z ↦ ⟪matrixAngleBaseProfile f T z, c z⟫) hi
  simpa only [matrixAngleAnsatz, matrixAngleCutoff, add_sub_cancel_left, smul_eq_mul] using h

omit [Fact (0 < C)] in
/-- The actual moment map is constant on every Hopf orbit, with its coefficient held fixed. -/
theorem matrixAngleMomentMap_flow (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C)
    (s : ℝ) (a : MatrixAngleCoefficients) :
    matrixAngleMomentMap f κ T (planarHopfFlow s z) a = matrixAngleMomentMap f κ T z a :=
  planarHopfAverage_flow _ z s

/-- Reflection of the actual planar map differentiates to reflection of its actual velocity. -/
theorem matrixAngleVelocity_reflection (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hreflect : ∀ z, f (-z) = planarReflection (f z)) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow f (-z) = planarReflection (orbitDeriv planarHopfFlow f z) := by
  have he (s : ℝ) : f (planarHopfFlow s (-z)) = planarReflection (f (planarHopfFlow s z)) := by
    rw [← planarHopfFlow_half z, ← planarHopfFlow_add, add_comm s (1 / 2),
      planarHopfFlow_add, planarHopfFlow_half, hreflect]
  have hl := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add f hf 0 (-z)
  have hr := planarReflectionLinearIsometryEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C) planarHopfFlow_add f hf 0 z)
  have heq : (fun s ↦ f (planarHopfFlow s (-z))) =
      (fun s ↦ planarReflection (f (planarHopfFlow s z))) := funext he
  rw [heq] at hl
  have h := hl.unique hr
  change orbitDeriv planarHopfFlow f (planarHopfFlow 0 (-z)) =
    planarReflection (orbitDeriv planarHopfFlow f (planarHopfFlow 0 z)) at h
  simpa only [planarHopfFlow_zero] using h

/-- The actual source s is even, t and b are odd under the antipodal reflection. -/
theorem matrixAngleProfiles_reflection (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hreflect : ∀ z, f (-z) = planarReflection (f z)) (z : PlanarHopfSphere C) :
    matrixPlanarS f (-z) = matrixPlanarS f z ∧
      matrixPlanarT f (-z) = -matrixPlanarT f z ∧
      matrixAngleNormalPosition f (-z) = -matrixAngleNormalPosition f z := by
  have hv := matrixAngleVelocity_reflection f hf hreflect z
  have hs : matrixPlanarS f (-z) = matrixPlanarS f z := by
    simpa only [matrixPlanarS, planarReflection_apply_zero] using
      congrArg (fun v : Planar ↦ v 0) hv
  have ht : matrixPlanarT f (-z) = -matrixPlanarT f z := by
    simpa only [matrixPlanarT, planarReflection_apply_one] using
      congrArg (fun v : Planar ↦ v 1) hv
  refine ⟨hs, ht, ?_⟩
  change matrixPlanarB f (-z) = -matrixPlanarB f z
  rw [matrixPlanarB_coordinates, matrixPlanarB_coordinates, hs, ht, hreflect]
  simp only [planarReflection_apply_zero, planarReflection_apply_one]
  ring

/-- Every literal correction direction is antipodally odd. -/
theorem matrixAngleBaseProfile_odd (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hreflect : ∀ z, f (-z) = planarReflection (f z)) (T : ℝ) (z : PlanarHopfSphere C) :
    matrixAngleBaseProfile f T (-z) = -matrixAngleBaseProfile f T z := by
  obtain ⟨hs, ht, hb⟩ := matrixAngleProfiles_reflection f hf hreflect z
  change orbitDeriv planarHopfFlow f (-z) 0 = orbitDeriv planarHopfFlow f z 0 at hs
  change orbitDeriv planarHopfFlow f (-z) 1 = -orbitDeriv planarHopfFlow f z 1 at ht
  ext i
  fin_cases i <;>
    simp [matrixAngleBaseProfile, matrixAngleMomentDirection, hs, ht, hb]

/-- With actual basic coefficients and odd curvature, the actual corrected angle is odd. -/
theorem matrixAngleAnsatz_basic_odd (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hreflect : ∀ z, f (-z) = planarReflection (f z))
    (κ : PlanarHopfSphere C → ℝ) (hκodd : ∀ z, κ (-z) = -κ z) (T : ℝ)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hbasic : ∀ z s, c (planarHopfFlow s z) = c z) (z : PlanarHopfSphere C) :
    matrixAngleAnsatz f κ T (c (-z)) (-z) = -matrixAngleAnsatz f κ T (c z) z := by
  have hc : c (-z) = c z := by simpa only [planarHopfFlow_half] using hbasic z (1 / 2)
  have ht := (matrixAngleProfiles_reflection f hf hreflect z).2.1
  change orbitDeriv planarHopfFlow f (-z) 1 = -orbitDeriv planarHopfFlow f z 1 at ht
  simp only [matrixAngleAnsatz, matrixAngleCutoff, hκodd, neg_sq, hc, ht,
    matrixAngleBaseProfile_odd f hf hreflect T z, inner_neg_left]
  ring

end GlobalEmbedding.Paper
