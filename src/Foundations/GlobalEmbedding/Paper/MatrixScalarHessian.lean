import GlobalEmbedding.Paper.MatrixScalarAnsatz
import GlobalEmbedding.Paper.MatrixScalarMomentCalculus
import GlobalEmbedding.Paper.MatrixNativePlanarProfiles
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual uniformly bounded coefficient Hessians for the scalar moments

Source: `main.tex`, `prop:matrix`, lines358–365.
DAG: `matrix-scalar-hessian`; exclusive owner W6.
The moment integrand is genuinely quadratic in the scalar, so its actual
coefficient Hessian is independent of the coefficient.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

variable {C m : ℕ}

/-- The literal second scalar derivative (0,2A), in the same Euclidean space.
Source: `prop:matrix`, lines358–365. -/
def matrixScalarMomentSecondDirection
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (z : PlanarHopfSphere C) : MatrixScalarCoefficients m :=
  WithLp.toLp 2 (fun i ↦ match i with
    | none => 0
    | some j => 2 * A z j)

/-- The actual pointwise coefficient Hessian, with its true two dual factors.
Source: `prop:matrix`, bounded second coefficient derivatives, line365. -/
def matrixScalarPointHessian
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ : PlanarHopfSphere C → ℝ) (q : ℝ) (z : PlanarHopfSphere C) :
    MatrixScalarCoefficients m →L[ℝ]
      MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
  matrixAngleCutoff κ z ^ 2 •
    (ContinuousLinearMap.toSpanSingleton ℝ
      ((ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentSecondDirection A z)).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A q z)))).comp
      (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
        (matrixScalarMomentDirection A q z))

/-- The actual period-integrated Hessian operator for the actual scalar moment map.
Source: `prop:matrix`, line365. -/
def matrixScalarHessian
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    MatrixScalarCoefficients m →L[ℝ]
      MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
  orbitAverage planarHopfFlow (fun w ↦ matrixScalarPointHessian A κ (u w) w) z

/-- The actual Jacobian integrand is affine in its coefficient, with derivative
exactly the literal pointwise Hessian. This is the actual quadratic calculation,
proved by continuous-linear-map extensionality and ordinary scalar ring identities.
Source: `prop:matrix`, bounded second derivatives, line365. -/
theorem matrixScalarPointJacobian_hasFDerivAt
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C)
    (a : MatrixScalarCoefficients m) :
    HasFDerivAt
      (fun b : MatrixScalarCoefficients m ↦ matrixAngleCutoff κ z •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u b z) z)).comp
            (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
              (matrixScalarMomentDirection A (u z) z)))
      (matrixScalarPointHessian A κ (u z) z) a := by
  let J : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
    matrixAngleCutoff κ z •
      (ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentDirection A (u z) z)).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A (u z) z))
  have he : (fun b : MatrixScalarCoefficients m ↦ matrixAngleCutoff κ z •
        (ContinuousLinearMap.toSpanSingleton ℝ
          (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u b z) z)).comp
            (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
              (matrixScalarMomentDirection A (u z) z))) =
      (fun b ↦ J + matrixScalarPointHessian A κ (u z) z b) := by
    funext b
    ext v i
    cases i <;>
      simp [J, matrixScalarPointHessian, matrixScalarAnsatz, matrixScalarMomentDirection,
        matrixScalarMomentSecondDirection]
    ring
  rw [he]
  exact (matrixScalarPointHessian A κ (u z) z).hasFDerivAt.const_add J

/-- Continuity of the actual second scalar derivative (0,2A).
Source: `prop:matrix`, bounded coefficient derivatives, line365. -/
theorem matrixScalarMomentSecondDirection_continuous
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m)) (hA : Continuous A) :
    Continuous (matrixScalarMomentSecondDirection A) := by
  apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_const
  | some j =>
    exact continuous_const.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin m) j).continuous.comp hA)

/-- Joint continuity of the actual pointwise Hessian in the scalar trial value
and actual sphere point. Source: `prop:matrix`, line365. -/
theorem matrixScalarPointHessian_continuous
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ : PlanarHopfSphere C → ℝ) (hA : Continuous A) (hκ : Continuous κ) :
    Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixScalarPointHessian A κ p.1 p.2) := by
  have hF := matrixScalarMomentDirection_continuous A hA
  have hK : Continuous (fun p : ℝ × PlanarHopfSphere C ↦
      matrixScalarMomentSecondDirection A p.2) :=
    (matrixScalarMomentSecondDirection_continuous A hA).comp continuous_snd
  have hρ : Continuous (fun p : ℝ × PlanarHopfSphere C ↦ matrixAngleCutoff κ p.2 ^ 2) :=
    (((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp (hκ.pow 2)).comp
      continuous_snd).pow 2
  have hR : Continuous (fun p : ℝ × PlanarHopfSphere C ↦
      (ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentSecondDirection A p.2)).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A p.1 p.2))) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ (MatrixScalarCoefficients m)).continuous.comp hK)
      |>.clm_comp ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).continuous.comp hF)
  exact hρ.smul
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ
      (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m)).continuous.comp hR).clm_comp
        ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).continuous.comp hF))

/-- The actual second coefficient Frechet derivative equals the literal averaged
Hessian at every coefficient; it is independent of that coefficient.

Proof: the actual first derivative was identified with its real period integral
in the scalar calculus module. Its pointwise integrand is affine in coefficient,
with the actual Hessian just proved. Apply the public genuine compact-period
differentiation theorem with continuous-linear maps as codomain, and identify
closed-period and interval integrals. Source: `prop:matrix`, line365. -/
theorem matrixScalarMomentMap_fderiv_fderiv [Fact (0 < C)]
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ)
    (hA : Continuous A) (hκ : Continuous κ) (hu : Continuous u)
    (z : PlanarHopfSphere C) (a : MatrixScalarCoefficients m) :
    fderiv ℝ (fderiv ℝ (matrixScalarMomentMap A κ u z)) a = matrixScalarHessian A κ u z := by
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
  let J : MatrixScalarCoefficients m × ℝ →
      MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m := fun p ↦
    matrixAngleCutoff κ (planarHopfFlow p.2 z) •
      (ContinuousLinearMap.toSpanSingleton ℝ
        (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u p.1 (planarHopfFlow p.2 z))
          (planarHopfFlow p.2 z))).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A (u (planarHopfFlow p.2 z)) (planarHopfFlow p.2 z)))
  have hJ : Continuous J :=
    (hρ.comp hw).smul
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ (MatrixScalarCoefficients m)).continuous.comp
        ((matrixScalarMomentDirection_continuous A hA).comp (hη.prodMk hw))).clm_comp
          ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).continuous.comp
            (hbase.comp hw)))
  let B : MatrixScalarCoefficients m × ℝ →
      MatrixScalarCoefficients m →L[ℝ]
        MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
    fun p ↦ matrixScalarPointHessian A κ (u (planarHopfFlow p.2 z)) (planarHopfFlow p.2 z)
  have hB : Continuous B := by
    have hpoint : Continuous (fun p : ℝ × PlanarHopfSphere C ↦
        matrixScalarPointHessian A κ p.1 p.2) := matrixScalarPointHessian_continuous A κ hA hκ
    have hpair : Continuous (fun p : MatrixScalarCoefficients m × ℝ ↦
        (u (planarHopfFlow p.2 z), planarHopfFlow p.2 z)) := (hu.comp hw).prodMk hw
    apply (hpoint.comp hpair).congr
    intro p
    rfl
  have h := hasFDerivAt_compact_period J B hJ hB
    (fun b t ↦ matrixScalarPointJacobian_hasFDerivAt A κ u (planarHopfFlow t z) b) a
  have hd : HasFDerivAt
      (fun b ↦ orbitAverage planarHopfFlow
        (fun w ↦ matrixAngleCutoff κ w •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u b w) w)).comp
              (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
                (matrixScalarMomentDirection A (u w) w))) z)
      (matrixScalarHessian A κ u z) a := by
    convert h using 1
    · funext b
      unfold orbitAverage
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    · unfold matrixScalarHessian orbitAverage
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have he : fderiv ℝ (matrixScalarMomentMap A κ u z) =
      (fun b ↦ orbitAverage planarHopfFlow
        (fun w ↦ matrixAngleCutoff κ w •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (matrixScalarMomentDirection A (matrixScalarAnsatz A κ u b w) w)).comp
              (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
                (matrixScalarMomentDirection A (u w) w))) z) := by
    funext b
    exact (matrixScalarMomentMap_hasFDerivAt A κ u hA hκ hu z b).fderiv
  rw [he]
  exact hd.fderiv

/-- Actual compactness of the fixed amplitudes bounds the literal Hessian
uniformly over every real frequency. No bound is supplied as a hypothesis.

Proof: η_b and r are bounded on the actual compact sphere, and |cos|≤1 bounds
every η_L in one fixed compact real interval. The actual pointwise Hessian is
continuous on that interval times the actual sphere, so compactness gives a
uniform operator bound. The genuine period has length one, hence its actual
Hessian integral satisfies the same bound. Source: `prop:matrix`, line365. -/
theorem matrixScalarHessian_uniform_bound [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hA : Continuous A) (hκ : Continuous κ) (hb : Continuous ηb) (hr : Continuous r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, ∀ z : PlanarHopfSphere C,
      ‖matrixScalarHessian A κ (matrixScalarOscillatoryBase f ηb r L) z‖ ≤ K := by
  obtain ⟨B0, hB0⟩ := (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    |>.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    |>.exists_bound_of_continuousOn hr.continuousOn
  let B : ℝ := |B0| + |B1|
  have htrial (L : ℝ) (w : PlanarHopfSphere C) :
      matrixScalarOscillatoryBase f ηb r L w ∈ Icc (-B) B := by
    apply abs_le.mp
    change |ηb w + r w * Real.cos (L * orbitDeriv planarHopfFlow f w 1)| ≤ B
    have hm : |r w * Real.cos (L * orbitDeriv planarHopfFlow f w 1)| ≤ |r w| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
        (mul_one _)
    calc
      _ ≤ |ηb w| + |r w * Real.cos (L * orbitDeriv planarHopfFlow f w 1)| := abs_add_le _ _
      _ ≤ B0 + B1 := add_le_add (hB0 w (mem_univ _)) (hm.trans (hB1 w (mem_univ _)))
      _ ≤ B := add_le_add (le_abs_self _) (le_abs_self _)
  have hswap : Continuous (fun p : PlanarHopfSphere C × ℝ ↦ (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hpoint : Continuous (fun p : ℝ × PlanarHopfSphere C ↦
      matrixScalarPointHessian A κ p.1 p.2) := matrixScalarPointHessian_continuous A κ hA hκ
  have hc : Continuous (fun p : PlanarHopfSphere C × ℝ ↦ matrixScalarPointHessian A κ p.2 p.1) := by
    apply (hpoint.comp hswap).congr
    intro p
    rfl
  have hn : Continuous (fun p : PlanarHopfSphere C × ℝ ↦
      ‖matrixScalarPointHessian A κ p.2 p.1‖) :=
    Continuous.norm (E := MatrixScalarCoefficients m →L[ℝ]
      MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) hc
  obtain ⟨K, hKn⟩ := ((isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C))).prod
    (isCompact_Icc : IsCompact (Icc (-B) B))).exists_bound_of_continuousOn hn.continuousOn
  have hK (p : PlanarHopfSphere C × ℝ) (hp : p ∈ univ ×ˢ Icc (-B) B) :
      ‖matrixScalarPointHessian A κ p.2 p.1‖ ≤ K := by
    have hv := hKn p hp
    change |‖matrixScalarPointHessian A κ p.2 p.1‖| ≤ K at hv
    exact (le_abs_self _).trans hv
  refine ⟨|K|, abs_nonneg _, ?_⟩
  intro L z
  change ‖∫ t in (0 : ℝ)..1, matrixScalarPointHessian A κ
    (matrixScalarOscillatoryBase f ηb r L (planarHopfFlow t z)) (planarHopfFlow t z)‖ ≤ |K|
  calc
    _ ≤ |K| * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ ↦
        (hK (planarHopfFlow t z, matrixScalarOscillatoryBase f ηb r L (planarHopfFlow t z))
          ⟨mem_univ _, htrial L _⟩).trans (le_abs_self K))
    _ = |K| := by norm_num

/-- The actual second Frechet derivatives of the actual scalar equations are
uniformly bounded for every frequency and every coefficient. This discharges
the true Hessian hypothesis needed for the accepted correction theorem.
Source: `prop:matrix`, bounded second coefficient derivatives, line365. -/
theorem matrixScalarMomentMap_uniform_hessian_bound [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hA : Continuous A) (hκ : Continuous κ) (hb : Continuous ηb) (hr : Continuous r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, ∀ z : PlanarHopfSphere C,
      ∀ a : MatrixScalarCoefficients m,
      ‖fderiv ℝ (fderiv ℝ
        (matrixScalarMomentMap A κ (matrixScalarOscillatoryBase f ηb r L) z)) a‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := matrixScalarHessian_uniform_bound f A κ ηb r hA hκ hb hr
  refine ⟨K, hK, ?_⟩
  intro L z a
  have ht := (matrix_planar_data_contMDiff f hf).2.1.continuous
  have hu : Continuous (matrixScalarOscillatoryBase f ηb r L) :=
    hb.add (hr.mul (Real.continuous_cos.comp (continuous_const.mul ht)))
  rw [matrixScalarMomentMap_fderiv_fderiv A κ _ hA hκ hu]
  exact hbound L z

#print axioms matrixScalarPointJacobian_hasFDerivAt
#print axioms matrixScalarMomentMap_fderiv_fderiv
#print axioms matrixScalarHessian_uniform_bound
#print axioms matrixScalarMomentMap_uniform_hessian_bound

end GlobalEmbedding.Paper
