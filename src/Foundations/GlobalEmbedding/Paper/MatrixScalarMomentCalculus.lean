import GlobalEmbedding.Paper.MatrixScalarAnsatz
import GlobalEmbedding.Paper.MatrixCompactPeriodDerivative
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import GlobalEmbedding.Paper.MatrixManifoldFlatCurvatureCutoff
import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual coefficient calculus of the scalar quadratic moments

Source: `main.tex`, `prop:matrix`, lines358–365.
DAG: `matrix-scalar-moment-calculus`.
The derivative of the literal averaged coefficient map is identified with the
literal integral Gram. No desired Jacobian or formal differentiation is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

variable {C m : ℕ}

/-- The true scalar moment values vary continuously with scalar and actual point.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentValues_continuous
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m)) (hA : Continuous A) :
    Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixScalarMomentValues A p.1 p.2) := by
  apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_fst
  | some j =>
    exact (continuous_fst.pow 2).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) j).continuous.comp hA).comp continuous_snd)

/-- The true scalar moment direction varies continuously with scalar and point.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentDirection_continuous
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m)) (hA : Continuous A) :
    Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixScalarMomentDirection A p.1 p.2) := by
  apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_const
  | some j =>
    exact (continuous_const.mul continuous_fst).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) j).continuous.comp hA).comp continuous_snd)

/-- The actual pointwise coefficient derivative is the actual rank-one operator.
Source: `prop:matrix`, lines358–360. -/
theorem matrixScalarMomentIntegrand_hasFDerivAt
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C)
    (a : MatrixScalarCoefficients m) :
    HasFDerivAt (fun b ↦ matrixScalarMomentValues A (matrixScalarAnsatz A κ u b z) z)
      (matrixAngleCutoff κ z •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u a z) z)).comp
            (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
              (matrixScalarMomentDirection A (u z) z))) a := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_smul] using
    (matrixScalarMomentValues_hasDerivAt A z (matrixScalarAnsatz A κ u a z)).hasFDerivAt.comp
      a (matrixScalarAnsatz_hasFDerivAt A κ u z a)

/-- The actual period-integrated coefficient derivative, justified by real compact
coefficient-ball domination and Mathlib's dominated differentiation theorem.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentMap_hasFDerivAt [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ)
    (hA : Continuous A) (hκ : Continuous κ) (hu : Continuous u)
    (z : PlanarHopfSphere C) (a : MatrixScalarCoefficients m) :
    HasFDerivAt (matrixScalarMomentMap A κ u z)
      (orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u a w) w)).comp
            (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
              (matrixScalarMomentDirection A (u w) w))) z) a := by
  have hbase : Continuous (fun w ↦ matrixScalarMomentDirection A (u w) w) :=
    (matrixScalarMomentDirection_continuous A hA).comp (hu.prodMk continuous_id)
  have hρ : Continuous (matrixAngleCutoff κ) :=
    (expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp (hκ.pow 2)
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have hw : Continuous (fun p : MatrixScalarCoefficients m × ℝ ↦ planarHopfFlow p.2 z) :=
    hflow.comp continuous_snd
  have hη : Continuous (fun p : MatrixScalarCoefficients m × ℝ ↦
      matrixScalarAnsatz A κ u p.1 (planarHopfFlow p.2 z)) :=
    (hu.comp hw).add ((hρ.comp hw).mul ((hbase.comp hw).inner continuous_fst))
  let F : MatrixScalarCoefficients m × ℝ → MatrixScalarCoefficients m := fun p ↦
    matrixScalarMomentValues A (matrixScalarAnsatz A κ u p.1 (planarHopfFlow p.2 z))
      (planarHopfFlow p.2 z)
  let L : MatrixScalarCoefficients m × ℝ →
      MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m := fun p ↦
    matrixAngleCutoff κ (planarHopfFlow p.2 z) •
      (ContinuousLinearMap.toSpanSingleton ℝ
        (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u p.1 (planarHopfFlow p.2 z))
          (planarHopfFlow p.2 z))).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A (u (planarHopfFlow p.2 z)) (planarHopfFlow p.2 z)))
  have hF : Continuous F :=
    (matrixScalarMomentValues_continuous A hA).comp (hη.prodMk hw)
  have hL : Continuous L :=
    (hρ.comp hw).smul
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ (MatrixScalarCoefficients m)).continuous.comp
        ((matrixScalarMomentDirection_continuous A hA).comp (hη.prodMk hw))).clm_comp
          ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).continuous.comp
            (hbase.comp hw)))
  have h := hasFDerivAt_compact_period F L hF hL
    (fun b t ↦ matrixScalarMomentIntegrand_hasFDerivAt A κ u (planarHopfFlow t z) b) a
  change HasFDerivAt (fun b ↦ matrixScalarMomentMap A κ u z b) _ a
  simpa only [F, L, matrixScalarMomentMap, orbitAverage,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] using h

/-- The actual Frechet derivative at zero is precisely the literal weighted Gram.
Source: `prop:matrix`, lines358–363. -/
theorem matrixScalarMomentMap_fderiv_zero [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ)
    (hA : Continuous A) (hκ : Continuous κ) (hu : Continuous u)
    (z : PlanarHopfSphere C) :
    fderiv ℝ (matrixScalarMomentMap A κ u z) 0 = matrixScalarGram A κ u z := by
  have h := matrixScalarMomentMap_hasFDerivAt A κ u hA hκ hu z 0
  simpa only [matrixScalarAnsatz_zero, matrixScalarGram] using h.fderiv

/-- The literal scalar variation profile is native smooth for actual smooth A and u.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentDirection_contMDiff [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (u : PlanarHopfSphere C → ℝ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixScalarCoefficients m) ∞
      (fun z ↦ matrixScalarMomentDirection A (u z) z) := by
  apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro i
  cases i with
  | none => exact contMDiff_const
  | some j =>
    exact (contMDiff_const.mul hu).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) j).contMDiff.comp hA)

/-- Actual joint native smoothness of the scalar trial in point and coefficient.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarAnsatz_contMDiff [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m)) 𝓘(ℝ, ℝ) ∞
      (fun p : PlanarHopfSphere C × MatrixScalarCoefficients m ↦
        matrixScalarAnsatz A κ u p.2 p.1) := by
  have hρ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixAngleCutoff κ) :=
    (manifold_flat_curvature_cutoff κ hκ).1
  have hbase := (matrixScalarMomentDirection_contMDiff A hA u hu).comp
    (contMDiff_fst : ContMDiff
      ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m))
      (planarHopfModel C) ∞ (fun p : PlanarHopfSphere C × MatrixScalarCoefficients m ↦ p.1))
  have hi : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m))
      𝓘(ℝ, ℝ) ∞ (fun p : PlanarHopfSphere C × MatrixScalarCoefficients m ↦
        ⟪matrixScalarMomentDirection A (u p.1) p.1, p.2⟫) :=
    (contDiff_inner (𝕜 := ℝ) (E := MatrixScalarCoefficients m)).contMDiff.comp
      (hbase.prodMk_space contMDiff_snd)
  exact (hu.comp contMDiff_fst).add ((hρ.comp contMDiff_fst).mul hi)

/-- Actual joint native smoothness of the true scalar moment integrands.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentIntegrand_contMDiff [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m))
      𝓘(ℝ, MatrixScalarCoefficients m) ∞
      (fun p : PlanarHopfSphere C × MatrixScalarCoefficients m ↦
        matrixScalarMomentValues A (matrixScalarAnsatz A κ u p.2 p.1) p.1) := by
  have hη := matrixScalarAnsatz_contMDiff A hA κ u hκ hu
  apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro i
  cases i with
  | none => exact hη
  | some j =>
    exact (hη.pow 2).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) j).contMDiff.comp hA).comp contMDiff_fst)

/-- The actual averaged scalar moment equation is jointly native smooth.
Proof: compose the literal smooth integrands with the actual smooth Hopf flow,
then reuse the accepted compact-parameter integral theorem.
Source: `prop:matrix`, lines358–365. -/
theorem matrixScalarMomentMap_contMDiff [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m))
      𝓘(ℝ, MatrixScalarCoefficients m) ∞
      (Function.uncurry (matrixScalarMomentMap A κ u)) := by
  let F : (PlanarHopfSphere C × MatrixScalarCoefficients m) × ℝ →
      MatrixScalarCoefficients m := fun p ↦ matrixScalarMomentValues A
    (matrixScalarAnsatz A κ u p.1.2 (planarHopfFlow p.2 p.1.1))
    (planarHopfFlow p.2 p.1.1)
  have hw : ContMDiff
      (((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m)).prod 𝓘(ℝ, ℝ))
      (planarHopfModel C) ∞ (fun p : (PlanarHopfSphere C × MatrixScalarCoefficients m) × ℝ ↦
        planarHopfFlow p.2 p.1.1) :=
    (planarHopfFlow_contMDiff C).comp
      (contMDiff_snd.prodMk (contMDiff_fst.comp contMDiff_fst))
  have hF : ContMDiff
      (((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, MatrixScalarCoefficients m) ∞ F :=
    (matrixScalarMomentIntegrand_contMDiff A hA κ u hκ hu).comp
      (hw.prodMk (contMDiff_snd.comp contMDiff_fst))
  have hM : IsManifold ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m)) ∞
      (PlanarHopfSphere C × MatrixScalarCoefficients m) := inferInstance
  let _ : ChartedSpace
      (EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixScalarCoefficients m)
      (PlanarHopfSphere C × MatrixScalarCoefficients m) :=
    inferInstanceAs (ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin (2 * C - 1))) (MatrixScalarCoefficients m))
      (PlanarHopfSphere C × MatrixScalarCoefficients m))
  let _ : IsManifold
      𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixScalarCoefficients m) ∞
      (PlanarHopfSphere C × MatrixScalarCoefficients m) := by
    simpa only [modelWithCornersSelf_prod] using hM
  have h := contMDiff_compact_parameter_integral
    (P := EuclideanSpace ℝ (Fin (2 * C - 1)) × MatrixScalarCoefficients m) (⊤ : ℕ∞) F
    (by simpa only [modelWithCornersSelf_prod] using hF)
  have hI : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixScalarCoefficients m))
      𝓘(ℝ, MatrixScalarCoefficients m) ∞
      (fun p : PlanarHopfSphere C × MatrixScalarCoefficients m ↦
        ∫ t in Icc (0 : ℝ) 1, F (p, t)) := by
    simpa only [modelWithCornersSelf_prod] using h
  apply hI.congr
  intro p
  change (∫ t in (0 : ℝ)..1,
    matrixScalarMomentValues A (matrixScalarAnsatz A κ u p.2 (planarHopfFlow t p.1))
      (planarHopfFlow t p.1)) = _
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- The actual coefficient equation is invariant when its base point moves along
an actual Hopf orbit; the coefficient is held fixed throughout the integral.
Source: `prop:matrix`, smooth basic corrections, line365. -/
theorem matrixScalarMomentMap_flow
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) (s : ℝ)
    (a : MatrixScalarCoefficients m) :
    matrixScalarMomentMap A κ u (planarHopfFlow s z) a = matrixScalarMomentMap A κ u z a :=
  planarHopfAverage_flow _ z s

/-- Every actual smooth coefficient field gives a scalar correction flat in all
native chart jets on the zero-curvature set.
Source: `prop:matrix`, lines365–366. -/
theorem matrixScalarAnsatz_sub_base_flat [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u)
    (c : PlanarHopfSphere C → MatrixScalarCoefficients m)
    (hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixScalarCoefficients m) ∞ c) :
    ManifoldFlatOn (I := planarHopfModel C)
      (fun z ↦ matrixScalarAnsatz A κ u (c z) z - u z) {z | κ z = 0} := by
  have hi : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ ⟪matrixScalarMomentDirection A (u z) z, c z⟫) :=
    (contDiff_inner (𝕜 := ℝ) (E := MatrixScalarCoefficients m)).contMDiff.comp
      ((matrixScalarMomentDirection_contMDiff A hA u hu).prodMk_space hc)
  have h := manifold_flat_curvature_cutoff_smul κ hκ
    (fun z ↦ ⟪matrixScalarMomentDirection A (u z) z, c z⟫) hi
  simpa only [matrixScalarAnsatz, matrixAngleCutoff, add_sub_cancel_left, smul_eq_mul] using h

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.matrixScalarMomentIntegrand_hasFDerivAt
#print axioms GlobalEmbedding.Paper.matrixScalarMomentMap_hasFDerivAt
#print axioms GlobalEmbedding.Paper.matrixScalarMomentMap_fderiv_zero

#print axioms GlobalEmbedding.Paper.matrixScalarMomentMap_contMDiff
#print axioms GlobalEmbedding.Paper.matrixScalarMomentMap_flow
#print axioms GlobalEmbedding.Paper.matrixScalarAnsatz_sub_base_flat
