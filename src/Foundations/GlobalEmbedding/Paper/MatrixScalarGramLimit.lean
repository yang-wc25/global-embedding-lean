import GlobalEmbedding.Paper.MatrixScalarMomentCalculus
import GlobalEmbedding.Paper.MatrixNativeAngleResidual
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.MatrixCompactPositiveOperatorBound
import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The actual scalar-moment Gram limit and its uniform inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, (3.6),
lines358–365. DAG: `matrix-scalar-gram-limit`; exclusive worker W1.
The same actual scalar Gram and Euclidean Option-indexed coefficient space are retained.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace Matrix NNReal

namespace GlobalEmbedding.Paper

/-- Finite scalar coefficient coordinates for the same actual Euclidean operators.
No Matrix norm instance is introduced; only temporary finite Pi coordinates are used. -/
def matrixScalarEntriesEquiv (m : ℕ) :
    (Option (Fin m) → Option (Fin m) → ℝ) ≃L[ℝ]
      (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) :=
  ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) :
    (Option (Fin m) → Option (Fin m) → ℝ) ≃ₗ[ℝ]
      (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m)).toContinuousLinearEquiv

/-- The actual operator coordinate equivalence has the literal matrix action. -/
theorem matrixScalarEntriesEquiv_apply {m : ℕ}
    (B : Option (Fin m) → Option (Fin m) → ℝ)
    (a : MatrixScalarCoefficients m) (i : Option (Fin m)) :
    matrixScalarEntriesEquiv m B a i = ∑ j, B i j * a j := rfl

/-- Actual scalar operator entries are standard Euclidean basis evaluations. -/
theorem matrixScalarEntriesEquiv_symm_apply {m : ℕ}
    (B : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m)
    (i j : Option (Fin m)) :
    (matrixScalarEntriesEquiv m).symm B i j = B (EuclideanSpace.single j 1) i := by
  have h := congrArg (fun Bop : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m ↦
    Bop (EuclideanSpace.single j 1) i) ((matrixScalarEntriesEquiv m).apply_symm_apply B)
  simpa only [matrixScalarEntriesEquiv_apply, PiLp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- The literal coefficient of cos(Lt) in the scalar variation profile: (0,2rA). -/
def matrixScalarOscillationDirection {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : MatrixScalarCoefficients m :=
  matrixScalarMomentDirection A (r z) z - EuclideanSpace.single none 1

/-- The scalar oscillation direction has zero scalar coordinate. -/
@[simp] theorem matrixScalarOscillationDirection_none {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    matrixScalarOscillationDirection A r z none = 0 := by
  simp [matrixScalarOscillationDirection, matrixScalarMomentDirection]

/-- Its actual vector coordinates are exactly 2rA. -/
@[simp] theorem matrixScalarOscillationDirection_some {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) (i : Fin m) :
    matrixScalarOscillationDirection A r z (some i) = 2 * r z * A z i := by
  simp [matrixScalarOscillationDirection, matrixScalarMomentDirection]

/-- The actual high-frequency profile is a fixed vector plus cos(Lt) times a fixed vector. -/
theorem matrixScalarMomentDirection_oscillatory {C m : ℕ}
    (f : PlanarHopfSphere C → Planar)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (ηb r : PlanarHopfSphere C → ℝ) (L : ℝ) (z : PlanarHopfSphere C) :
    matrixScalarMomentDirection A (matrixScalarOscillatoryBase f ηb r L z) z =
      matrixScalarMomentDirection A (ηb z) z +
        Real.cos (L * matrixPlanarT f z) • matrixScalarOscillationDirection A r z := by
  ext i
  cases i with
  | none => simp [matrixScalarMomentDirection]
  | some i =>
    simp [matrixScalarMomentDirection, matrixScalarOscillatoryBase, matrixPlanarT]
    ring

/-- The literal nonoscillatory limiting rank-one integrand, retaining the same l² operators. -/
def matrixScalarGramLimitIntegrand {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ ηb r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
  matrixAngleCutoff κ z •
    ((ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentDirection A (ηb z) z)).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A (ηb z) z)) +
      (1 / 2 : ℝ) •
        (ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarOscillationDirection A r z)).comp
          (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
            (matrixScalarOscillationDirection A r z)))

/-- The actual nonoscillatory scalar Gram limit; this does not replace the original G_L. -/
def matrixScalarGramLimit {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ ηb r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
  orbitAverage planarHopfFlow (matrixScalarGramLimitIntegrand A κ ηb r) z

/-- The genuine vector part of an Option-indexed Euclidean coefficient. -/
def matrixScalarVectorPart {m : ℕ} (a : MatrixScalarCoefficients m) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i ↦ a (some i))

/-- The actual scalar direction pairs with the coefficient as c+2q inner(A,b). -/
theorem matrixScalarMomentDirection_inner {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (z : PlanarHopfSphere C) (q : ℝ) (a : MatrixScalarCoefficients m) :
    ⟪matrixScalarMomentDirection A q z, a⟫ =
      a none + 2 * q * ⟪A z, matrixScalarVectorPart a⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    matrixScalarMomentDirection, matrixScalarVectorPart, Pi.star_apply, star_trivial,
    Fintype.sum_option, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The oscillation direction pairs as exactly 2r inner(A,b). -/
theorem matrixScalarOscillationDirection_inner {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (r : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C)
    (a : MatrixScalarCoefficients m) :
    ⟪matrixScalarOscillationDirection A r z, a⟫ =
      2 * r z * ⟪A z, matrixScalarVectorPart a⟫ := by
  rw [matrixScalarOscillationDirection, inner_sub_left, matrixScalarMomentDirection_inner]
  simp [EuclideanSpace.inner_single_left]

/-- The fixed actual frequency-L amplitude in each scalar Gram entry. -/
def matrixScalarGramAmplitudeOne {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ ηb r : PlanarHopfSphere C → ℝ) (i j : Option (Fin m))
    (w : PlanarHopfSphere C) : ℝ :=
  matrixAngleCutoff κ w *
    (matrixScalarMomentDirection A (ηb w) w i * matrixScalarOscillationDirection A r w j +
      matrixScalarOscillationDirection A r w i * matrixScalarMomentDirection A (ηb w) w j)

/-- The fixed actual frequency-2L amplitude in each scalar Gram entry. -/
def matrixScalarGramAmplitudeTwo {C m : ℕ}
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ r : PlanarHopfSphere C → ℝ) (i j : Option (Fin m))
    (w : PlanarHopfSphere C) : ℝ :=
  (1 / 2 : ℝ) * matrixAngleCutoff κ w * matrixScalarOscillationDirection A r w i *
    matrixScalarOscillationDirection A r w j

section Smooth
variable {C m : ℕ} [Fact (0 < C)]

/-- The actual fixed oscillation direction is native smooth from actual smooth data. -/
theorem matrixScalarOscillationDirection_contMDiff
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (r : PlanarHopfSphere C → ℝ)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixScalarCoefficients m) ∞
      (matrixScalarOscillationDirection A r) :=
  (matrixScalarMomentDirection_contMDiff A hA r hr).sub contMDiff_const

/-- Native smooth fixed data give an actual continuous limiting scalar Gram field.

Proof: actual direction smoothness, fixed dual/rank-one CLMs and native algebra give a
smooth integrand. The accepted actual Hopf averaging theorem preserves native smoothness.
Source: prop:matrix, continuous positive limiting Gram in (3.6). -/
theorem matrix_scalar_gram_limit_integrand_contMDiff
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r) :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) ∞
      (matrixScalarGramLimitIntegrand A κ ηb r) := by
  have h0 := matrixScalarMomentDirection_contMDiff A hA ηb hb
  have h1 := matrixScalarOscillationDirection_contMDiff A hA r hr
  have hρ := expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  have hI : ContMDiff (planarHopfModel C)
      𝓘(ℝ, MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) ∞
      (matrixScalarGramLimitIntegrand A κ ηb r) := by
    exact hρ.smul
      ((((ContinuousLinearMap.toSpanSingletonLIE ℝ
          (MatrixScalarCoefficients m)).toContinuousLinearMap.contMDiff.comp h0).clm_comp
        ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).toContinuousLinearMap.contMDiff.comp
          h0)).add
        ((contMDiff_const : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
          (fun _ : PlanarHopfSphere C ↦ (1 / 2 : ℝ))).smul
          (((ContinuousLinearMap.toSpanSingletonLIE ℝ
              (MatrixScalarCoefficients m)).toContinuousLinearMap.contMDiff.comp h1).clm_comp
            ((InnerProductSpace.toDual ℝ
              (MatrixScalarCoefficients m)).toContinuousLinearMap.contMDiff.comp h1))))
  exact hI

/-- The actual limiting scalar Gram field is native smooth, hence genuinely continuous. -/
theorem matrix_scalar_gram_limit_contMDiff
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r) :
    ContMDiff (planarHopfModel C)
      𝓘(ℝ, MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) ∞
      (matrixScalarGramLimit A κ ηb r) :=
  planarHopfAverage_contMDiff _
    (matrix_scalar_gram_limit_integrand_contMDiff A hA κ ηb r hκ hb hr)

/-- The same actual scalar Gram has the literal weighted direction-product entries.

Proof: actual smooth direction/cutoff data give a continuous, genuinely integrable
rank-one field. Apply the fixed operator evaluation/projection CLM to commute with its
actual period integral. Source: prop:matrix, the actual derivative Gram in (3.6). -/
theorem matrix_scalar_gram_entries
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ u : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u)
    (z : PlanarHopfSphere C) (i j : Option (Fin m)) :
    (matrixScalarEntriesEquiv m).symm (matrixScalarGram A κ u z) i j =
      orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w *
        matrixScalarMomentDirection A (u w) w i * matrixScalarMomentDirection A (u w) w j) z := by
  have hF := (matrixScalarMomentDirection_contMDiff A hA u hu).continuous
  have hρ := (expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)).continuous
  let B : PlanarHopfSphere C → MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
    fun w ↦ matrixAngleCutoff κ w •
      (ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentDirection A (u w) w)).comp
        (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
          (matrixScalarMomentDirection A (u w) w))
  have hBc : Continuous B := hρ.smul
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ (MatrixScalarCoefficients m)).continuous.comp hF).clm_comp
      ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)).continuous.comp hF))
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  let Q : (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).comp
      (ContinuousLinearMap.apply ℝ (MatrixScalarCoefficients m) (EuclideanSpace.single j 1))
  rw [matrixScalarEntriesEquiv_symm_apply]
  change Q (∫ t in (0 : ℝ)..1, B (planarHopfFlow t z)) = _
  have hi : IntervalIntegrable (fun t : ℝ ↦ B (planarHopfFlow t z)) volume 0 1 :=
    (hBc.comp hR).intervalIntegrable _ _
  rw [← Q.intervalIntegral_comp_comm hi]
  change _ = ∫ t in (0 : ℝ)..1, _
  apply intervalIntegral.integral_congr
  intro t _
  simp [Q, B, EuclideanSpace.inner_single_right]
  ring

/-- The limiting operator entries are exactly the average of the two fixed outer products.

Proof: commute the same fixed operator-coordinate CLM with the actual integrable limiting
operator field. Source: prop:matrix, the nonoscillatory limit in (3.6). -/
theorem matrix_scalar_gram_limit_entries
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (z : PlanarHopfSphere C) (i j : Option (Fin m)) :
    (matrixScalarEntriesEquiv m).symm (matrixScalarGramLimit A κ ηb r z) i j =
      orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w *
        (matrixScalarMomentDirection A (ηb w) w i * matrixScalarMomentDirection A (ηb w) w j +
          (1 / 2 : ℝ) * matrixScalarOscillationDirection A r w i *
            matrixScalarOscillationDirection A r w j)) z := by
  have hB := (matrix_scalar_gram_limit_integrand_contMDiff A hA κ ηb r hκ hb hr).continuous
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  let Q : (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).comp
      (ContinuousLinearMap.apply ℝ (MatrixScalarCoefficients m) (EuclideanSpace.single j 1))
  rw [matrixScalarEntriesEquiv_symm_apply]
  change Q (∫ t in (0 : ℝ)..1, matrixScalarGramLimitIntegrand A κ ηb r (planarHopfFlow t z)) = _
  have hi : IntervalIntegrable (fun t : ℝ ↦
      matrixScalarGramLimitIntegrand A κ ηb r (planarHopfFlow t z)) volume 0 1 :=
    (hB.comp hR).intervalIntegrable _ _
  rw [← Q.intervalIntegral_comp_comm hi]
  change _ = ∫ t in (0 : ℝ)..1, _
  apply intervalIntegral.integral_congr
  intro t _
  simp [Q, matrixScalarGramLimitIntegrand, EuclideanSpace.inner_single_right]
  ring

/-- The limiting entries are precisely the original scalar/vector block formulas.

Proof: substitute the actual none/some direction coordinates into the actual limiting
entry integral and simplify the scalar polynomial. Source: prop:matrix, (3.6). -/
theorem matrix_scalar_gram_limit_entry_cases
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (z : PlanarHopfSphere C) (i j : Option (Fin m)) :
    (matrixScalarEntriesEquiv m).symm (matrixScalarGramLimit A κ ηb r z) i j =
      match i, j with
      | none, none => orbitAverage planarHopfFlow (matrixAngleCutoff κ) z
      | none, some j => orbitAverage planarHopfFlow
          (fun w ↦ 2 * matrixAngleCutoff κ w * ηb w * A w j) z
      | some i, none => orbitAverage planarHopfFlow
          (fun w ↦ 2 * matrixAngleCutoff κ w * ηb w * A w i) z
      | some i, some j => orbitAverage planarHopfFlow
          (fun w ↦ 4 * matrixAngleCutoff κ w * A w i * A w j *
            (ηb w ^ 2 + r w ^ 2 / 2)) z := by
  rw [matrix_scalar_gram_limit_entries A hA κ ηb r hκ hb hr]
  cases i <;> cases j <;>
    apply congrArg (fun g : PlanarHopfSphere C → ℝ ↦ orbitAverage planarHopfFlow g z)
  all_goals
    funext w
    simp only [matrixScalarMomentDirection, matrixScalarOscillationDirection_none,
      matrixScalarOscillationDirection_some]
    ring

/-- The actual limiting quadratic form is the actual nonnegative expression of (3.6).

Proof: a fixed continuous linear functional evaluates a limiting operator on the coefficient
and pairs with that same coefficient. Commute it with the actual integrable operator
average. The exact none/vector inner-product formulas give the two squares pointwise.
Source: prop:matrix, equation(3.6), with r²=2rho in the actual density application. -/
theorem matrix_scalar_gram_limit_quadratic_average
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (z : PlanarHopfSphere C) (a : MatrixScalarCoefficients m) :
    ⟪matrixScalarGramLimit A κ ηb r z a, a⟫ =
      orbitAverage planarHopfFlow (fun w ↦
        matrixAngleCutoff κ w * (a none + 2 * ηb w * ⟪A w, matrixScalarVectorPart a⟫) ^ 2 +
          2 * matrixAngleCutoff κ w * r w ^ 2 * ⟪A w, matrixScalarVectorPart a⟫ ^ 2) z := by
  have hB := (matrix_scalar_gram_limit_integrand_contMDiff A hA κ ηb r hκ hb hr).continuous
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  let Q : (MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) →L[ℝ] ℝ :=
    (innerSL ℝ a).comp (ContinuousLinearMap.apply ℝ (MatrixScalarCoefficients m) a)
  have hq : ⟪matrixScalarGramLimit A κ ηb r z a, a⟫ =
      Q (matrixScalarGramLimit A κ ηb r z) := real_inner_comm _ _
  rw [hq]
  change Q (∫ t in (0 : ℝ)..1, matrixScalarGramLimitIntegrand A κ ηb r (planarHopfFlow t z)) = _
  have hi : IntervalIntegrable (fun t : ℝ ↦
      matrixScalarGramLimitIntegrand A κ ηb r (planarHopfFlow t z)) volume 0 1 :=
    (hB.comp hR).intervalIntegrable _ _
  rw [← Q.intervalIntegral_comp_comm hi]
  change _ = ∫ t in (0 : ℝ)..1, _
  apply intervalIntegral.integral_congr
  intro t _
  have h0 : ⟪a, matrixScalarMomentDirection A (ηb (planarHopfFlow t z))
      (planarHopfFlow t z)⟫ =
      a none + 2 * ηb (planarHopfFlow t z) * ⟪A (planarHopfFlow t z), matrixScalarVectorPart a⟫ :=
    (real_inner_comm _ _).trans (matrixScalarMomentDirection_inner A _ _ a)
  have h1 : ⟪a, matrixScalarOscillationDirection A r (planarHopfFlow t z)⟫ =
      2 * r (planarHopfFlow t z) * ⟪A (planarHopfFlow t z), matrixScalarVectorPart a⟫ :=
    (real_inner_comm _ _).trans (matrixScalarOscillationDirection_inner A r _ a)
  simp [Q, matrixScalarGramLimitIntegrand, inner_add_right, inner_smul_right,
    h0, h1, matrixScalarMomentDirection_inner, matrixScalarOscillationDirection_inner]
  ring

/-- The limiting quadratic form in exactly the original two-average form of (3.6).

Proof: use the actual quadratic average identity. Both continuous summands are genuinely
period integrable, so split their actual integral and pull out the fixed factor2.
Source: prop:matrix,(3.6), with r²=2rho. -/
theorem matrix_scalar_gram_limit_quadratic
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (z : PlanarHopfSphere C) (a : MatrixScalarCoefficients m) :
    ⟪matrixScalarGramLimit A κ ηb r z a, a⟫ =
      orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w *
        (a none + 2 * ηb w * ⟪A w, matrixScalarVectorPart a⟫) ^ 2) z +
      2 * orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w * r w ^ 2 *
        ⟪A w, matrixScalarVectorPart a⟫ ^ 2) z := by
  let q0 : PlanarHopfSphere C → ℝ := fun w ↦ matrixAngleCutoff κ w *
    (a none + 2 * ηb w * ⟪A w, matrixScalarVectorPart a⟫) ^ 2
  let q1 : PlanarHopfSphere C → ℝ := fun w ↦ matrixAngleCutoff κ w * r w ^ 2 *
    ⟪A w, matrixScalarVectorPart a⟫ ^ 2
  have hρ : Continuous (matrixAngleCutoff κ) :=
    (expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)).continuous
  have hv : Continuous (fun w ↦ ⟪A w, matrixScalarVectorPart a⟫) :=
    hA.continuous.inner continuous_const
  have h0 : Continuous q0 := hρ.mul
    ((continuous_const.add ((continuous_const.mul hb.continuous).mul hv)).pow 2)
  have h1 : Continuous q1 := (hρ.mul (hr.continuous.pow 2)).mul (hv.pow 2)
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hi0 : IntervalIntegrable (fun t : ℝ ↦ q0 (planarHopfFlow t z)) volume 0 1 :=
    (h0.comp hR).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ 2 * q1 (planarHopfFlow t z)) volume 0 1 :=
    (continuous_const.mul (h1.comp hR)).intervalIntegrable _ _
  rw [matrix_scalar_gram_limit_quadratic_average A hA κ ηb r hκ hb hr]
  have he : (fun w ↦ matrixAngleCutoff κ w *
      (a none + 2 * ηb w * ⟪A w, matrixScalarVectorPart a⟫) ^ 2 +
        2 * matrixAngleCutoff κ w * r w ^ 2 * ⟪A w, matrixScalarVectorPart a⟫ ^ 2) =
      (fun w ↦ q0 w + 2 * q1 w) := by
    funext w
    dsimp only [q0, q1]
    ring
  rw [he]
  change (∫ t in (0 : ℝ)..1, q0 (planarHopfFlow t z) + 2 * q1 (planarHopfFlow t z)) = _
  rw [intervalIntegral.integral_add hi0 hi1, intervalIntegral.integral_const_mul]
  rfl

/-- The actual limiting scalar Gram is positive on all nonzero actual coefficients,
including the purely scalar case m=0.

Proof: its actual quadratic average is nonnegative. If the vector coefficient is nonzero,
actual positive orbit support and r>0 off curvature zero make its second summand strictly
positive at an actual orbit point. If the vector part is zero, the scalar coefficient is
nonzero, and an actual nonzero-curvature point from the actual selector's curvature signs
makes the first summand positive. Shift that point to time zero, apply actual continuous
period-integral positivity, and use actual Hopf-average invariance. Source: prop:matrix,(3.6). -/
theorem matrix_scalar_gram_limit_positive
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (hrpos : ∀ w, planarOrbitCurvature planarHopfFlow f w ≠ 0 → 0 < r w)
    (hspan : ∀ z, ∀ b : EuclideanSpace ℝ (Fin m), b ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) ≠ 0 ∧
        0 < ⟪A (planarHopfFlow t z), b⟫)
    (z : PlanarHopfSphere C) (a : MatrixScalarCoefficients m) (ha : a ≠ 0) :
    0 < ⟪matrixScalarGramLimit A (planarOrbitCurvature planarHopfFlow f) ηb r z a, a⟫ := by
  let κ := planarOrbitCurvature planarHopfFlow f
  let b := matrixScalarVectorPart a
  let q : PlanarHopfSphere C → ℝ := fun w ↦
    matrixAngleCutoff κ w * (a none + 2 * ηb w * ⟪A w, b⟫) ^ 2 +
      2 * matrixAngleCutoff κ w * r w ^ 2 * ⟪A w, b⟫ ^ 2
  have hρ : Continuous (matrixAngleCutoff κ) :=
    (expNegInvGlue.contDiff.contMDiff.comp (hf.curvature_smooth.pow 2)).continuous
  have hinner : Continuous (fun w ↦ ⟪A w, b⟫) := hA.continuous.inner continuous_const
  have hq : Continuous q :=
    (hρ.mul ((continuous_const.add ((continuous_const.mul hb.continuous).mul hinner)).pow 2)).add
      (((continuous_const.mul hρ).mul (hr.continuous.pow 2)).mul (hinner.pow 2))
  have hn (w : PlanarHopfSphere C) : 0 ≤ q w := by
    have hρw : 0 ≤ matrixAngleCutoff κ w := expNegInvGlue.nonneg _
    dsimp only [q]
    positivity
  have hpoint : ∃ t : ℝ, 0 < q (planarHopfFlow t z) := by
    by_cases hbzero : b = 0
    · have hc : a none ≠ 0 := by
        intro hc
        apply ha
        ext i
        cases i with
        | none => exact hc
        | some j =>
          have hj := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) hbzero
          simpa [b, matrixScalarVectorPart] using hj
      obtain ⟨_, t, _, ht⟩ := hf.curvature_signs z
      have hcut : 0 < matrixAngleCutoff κ (planarHopfFlow t z) :=
        expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero ht.ne')
      refine ⟨t, ?_⟩
      simpa only [q, hbzero, inner_zero_right, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)]
        using mul_pos hcut (sq_pos_of_ne_zero hc)
    · obtain ⟨t, hk, hp⟩ := hspan z b hbzero
      have hcut : 0 < matrixAngleCutoff κ (planarHopfFlow t z) :=
        expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hk)
      have hrp := hrpos (planarHopfFlow t z) hk
      have hsecond : 0 < 2 * matrixAngleCutoff κ (planarHopfFlow t z) *
          r (planarHopfFlow t z) ^ 2 * ⟪A (planarHopfFlow t z), b⟫ ^ 2 :=
        mul_pos (mul_pos (mul_pos (by norm_num) hcut) (sq_pos_of_pos hrp)) (sq_pos_of_pos hp)
      refine ⟨t, ?_⟩
      dsimp only [q]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hcut.le (sq_nonneg _)) hsecond
  obtain ⟨t, ht⟩ := hpoint
  have hR : Continuous (fun s : ℝ ↦ planarHopfFlow s (planarHopfFlow t z)) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hp : 0 < orbitAverage planarHopfFlow q (planarHopfFlow t z) := by
    unfold orbitAverage
    apply intervalIntegral.integral_pos (by norm_num) (hq.comp hR).continuousOn
      (fun s _ ↦ hn _)
    exact ⟨0, by norm_num, by simpa only [Function.comp_apply, planarHopfFlow_zero] using ht⟩
  rw [matrix_scalar_gram_limit_quadratic_average A hA _ ηb r hf.curvature_smooth hb hr]
  change 0 < orbitAverage planarHopfFlow q z
  simpa only [planarHopfAverage_flow] using hp

/-- Both actual scalar Gram oscillatory amplitudes are native smooth fixed data.
Both amplitudes stay fixed while the actual frequency varies. -/
theorem matrix_scalar_gram_amplitudes_contMDiff
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r) (i j : Option (Fin m)) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixScalarGramAmplitudeOne A κ ηb r i j) ∧
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixScalarGramAmplitudeTwo A κ r i j) := by
  have h0 := matrixScalarMomentDirection_contMDiff A hA ηb hb
  have h1 := matrixScalarOscillationDirection_contMDiff A hA r hr
  have h0i := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).contMDiff.comp h0
  have h0j := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) j).contMDiff.comp h0
  have h1i := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).contMDiff.comp h1
  have h1j := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) j).contMDiff.comp h1
  have hρ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixAngleCutoff κ) :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  exact ⟨hρ.mul ((h0i.mul h1j).add (h1i.mul h0j)),
    ((contMDiff_const.mul hρ).mul h1i).mul h1j⟩

/-- Every actual high-frequency scalar Gram entry equals its true limiting entry plus
actual fixed-amplitude oscillatory averages at L and2L.

Proof: expand the literal F_L=F0+cos(Lt)F1 outer product and use the exact double-angle
identity. Actual fixed amplitudes and phase are smooth/continuous and hence genuinely
period integrable before splitting the actual average. Source: prop:matrix,(3.6). -/
theorem matrix_scalar_gram_entry_decomposition
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (L : ℝ) (z : PlanarHopfSphere C) (i j : Option (Fin m)) :
    (matrixScalarEntriesEquiv m).symm (matrixScalarGram A
        (planarOrbitCurvature planarHopfFlow f) (matrixScalarOscillatoryBase f ηb r L) z) i j =
      (matrixScalarEntriesEquiv m).symm
          (matrixScalarGramLimit A (planarOrbitCurvature planarHopfFlow f) ηb r z) i j +
        orbitAverage planarHopfFlow (fun w ↦ matrixScalarGramAmplitudeOne A
          (planarOrbitCurvature planarHopfFlow f) ηb r i j w *
          Real.cos (L * matrixPlanarT f w)) z +
        orbitAverage planarHopfFlow (fun w ↦ matrixScalarGramAmplitudeTwo A
          (planarOrbitCurvature planarHopfFlow f) r i j w *
          Real.cos ((2 * L) * matrixPlanarT f w)) z := by
  let κ := planarOrbitCurvature planarHopfFlow f
  let u := matrixScalarOscillatoryBase f ηb r L
  have ht := (matrix_planar_data_contMDiff f hf.smooth).2.1
  have hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u :=
    hb.add (hr.mul (Real.contDiff_cos.contMDiff.comp (contMDiff_const.mul ht)))
  let v0 := fun w ↦ matrixScalarMomentDirection A (ηb w) w
  let v1 := matrixScalarOscillationDirection A r
  let a0 : PlanarHopfSphere C → ℝ := fun w ↦ matrixAngleCutoff κ w *
    (v0 w i * v0 w j + (1 / 2 : ℝ) * v1 w i * v1 w j)
  let a1 := matrixScalarGramAmplitudeOne A κ ηb r i j
  let a2 := matrixScalarGramAmplitudeTwo A κ r i j
  have h0 := (matrixScalarMomentDirection_contMDiff A hA ηb hb).continuous
  have h1 := (matrixScalarOscillationDirection_contMDiff A hA r hr).continuous
  have h0i := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).continuous.comp h0
  have h0j := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) j).continuous.comp h0
  have h1i := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).continuous.comp h1
  have h1j := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) j).continuous.comp h1
  have hρ : Continuous (matrixAngleCutoff κ) :=
    (expNegInvGlue.contDiff.contMDiff.comp (hf.curvature_smooth.pow 2)).continuous
  have ha0 : Continuous a0 := hρ.mul
    ((h0i.mul h0j).add ((continuous_const.mul h1i).mul h1j))
  have hamp := matrix_scalar_gram_amplitudes_contMDiff A hA κ ηb r hf.curvature_smooth hb hr i j
  have ha1 : Continuous a1 := hamp.1.continuous
  have ha2 : Continuous a2 := hamp.2.continuous
  have he (w : PlanarHopfSphere C) :
      matrixAngleCutoff κ w * matrixScalarMomentDirection A (u w) w i *
          matrixScalarMomentDirection A (u w) w j =
      (a0 w + a1 w * Real.cos (L * matrixPlanarT f w)) +
        a2 w * Real.cos ((2 * L) * matrixPlanarT f w) := by
    dsimp only [u]
    simp only [matrixScalarMomentDirection_oscillatory, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    rw [show (2 * L) * matrixPlanarT f w = 2 * (L * matrixPlanarT f w) by ring,
      Real.cos_two_mul]
    dsimp only [a0, a1, a2, matrixScalarGramAmplitudeOne, matrixScalarGramAmplitudeTwo, v0, v1]
    ring
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hi0 : IntervalIntegrable (fun t : ℝ ↦ a0 (planarHopfFlow t z)) volume 0 1 :=
    (ha0.comp hR).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ a1 (planarHopfFlow t z) *
      Real.cos (L * matrixPlanarT f (planarHopfFlow t z))) volume 0 1 :=
    ((ha1.comp hR).mul
      (Real.continuous_cos.comp (continuous_const.mul (ht.continuous.comp hR)))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ a2 (planarHopfFlow t z) *
      Real.cos ((2 * L) * matrixPlanarT f (planarHopfFlow t z))) volume 0 1 :=
    ((ha2.comp hR).mul
      (Real.continuous_cos.comp (continuous_const.mul (ht.continuous.comp hR)))).intervalIntegrable _ _
  rw [matrix_scalar_gram_entries A hA κ u hf.curvature_smooth hu,
    matrix_scalar_gram_limit_entries A hA κ ηb r hf.curvature_smooth hb hr]
  have hfun : (fun w ↦ matrixAngleCutoff κ w *
      matrixScalarMomentDirection A (u w) w i * matrixScalarMomentDirection A (u w) w j) =
      (fun w ↦ (a0 w + a1 w * Real.cos (L * matrixPlanarT f w)) +
        a2 w * Real.cos ((2 * L) * matrixPlanarT f w)) := funext he
  rw [hfun]
  change (∫ t in (0 : ℝ)..1, (a0 (planarHopfFlow t z) + a1 (planarHopfFlow t z) *
      Real.cos (L * matrixPlanarT f (planarHopfFlow t z))) + a2 (planarHopfFlow t z) *
      Real.cos ((2 * L) * matrixPlanarT f (planarHopfFlow t z))) = _
  rw [intervalIntegral.integral_add (hi0.add hi1) hi2, intervalIntegral.integral_add hi0 hi1]
  rfl

/-- The SAME actual scalar Gram converges uniformly in its original Euclidean operator
norm to the actual nonoscillatory limit, for every m including0.

Proof: each exact entry error is the sum of the two actual fixed-amplitude averages just
identified. Accepted Hopf oscillatory decay applies at L and2L. Finite Option-index entry
convergence is convergence to zero along atTop times the top base filter. The fixed actual
Euclidean operator coordinate equivalence transfers it to the original operator space;
uniform difference convergence is uniform convergence to the actual limit. Source:(3.6). -/
theorem matrix_scalar_gram_tendsto_uniformly
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r) :
    TendstoUniformly (fun L : ℝ ↦ matrixScalarGram A
        (planarOrbitCurvature planarHopfFlow f) (matrixScalarOscillatoryBase f ηb r L))
      (matrixScalarGramLimit A (planarOrbitCurvature planarHopfFlow f) ηb r) atTop := by
  let κ := planarOrbitCurvature planarHopfFlow f
  let G := fun L z ↦ matrixScalarGram A κ (matrixScalarOscillatoryBase f ηb r L) z
  let G0 := matrixScalarGramLimit A κ ηb r
  have hcoord (i j : Option (Fin m)) : TendstoUniformly
      (fun L : ℝ ↦ fun z ↦ (matrixScalarEntriesEquiv m).symm (G L z - G0 z) i j)
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
    have hamp := matrix_scalar_gram_amplitudes_contMDiff A hA κ ηb r hf.curvature_smooth hb hr i j
    have hc1 := matrix_hopf_uniform_oscillatory_average f hf.smooth hf.unit_speed hf.orbit_analytic
      (matrixScalarGramAmplitudeOne A κ ηb r i j) hamp.1 0
    have hc2 : TendstoUniformly (fun L : ℝ ↦ orbitAverage planarHopfFlow
        (fun w ↦ matrixScalarGramAmplitudeTwo A κ r i j w *
          Real.cos ((2 * L) * matrixPlanarT f w + 0)))
        (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
      intro V hV
      exact (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
        ((matrix_hopf_uniform_oscillatory_average f hf.smooth hf.unit_speed hf.orbit_analytic
          (matrixScalarGramAmplitudeTwo A κ r i j) hamp.2 0) V hV)
    have hc := hc1.add hc2
    simp only [add_zero] at hc
    convert hc using 1
    · funext L z
      simp only [map_sub, Pi.sub_apply, Pi.add_apply]
      dsimp only [G, G0, κ]
      rw [matrix_scalar_gram_entry_decomposition f hf A hA ηb r hb hr]
      ring
    · funext z
      simp
  have hpi : Tendsto
      (fun p : ℝ × PlanarHopfSphere C ↦ fun i j : Option (Fin m) ↦
        (matrixScalarEntriesEquiv m).symm (G p.1 p.2 - G0 p.2) i j)
      (atTop ×ˢ ⊤) (𝓝 (0 : Option (Fin m) → Option (Fin m) → ℝ)) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦
      tendsto_prod_top_iff.mpr (hcoord i j)
  have hop : Tendsto (fun p : ℝ × PlanarHopfSphere C ↦ G p.1 p.2 - G0 p.2)
      (atTop ×ˢ ⊤) (𝓝 (0 : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m)) := by
    have h := (matrixScalarEntriesEquiv m).continuous.continuousAt.tendsto.comp hpi
    change Tendsto (fun p : ℝ × PlanarHopfSphere C ↦ matrixScalarEntriesEquiv m
      ((matrixScalarEntriesEquiv m).symm (G p.1 p.2 - G0 p.2)))
      (atTop ×ˢ ⊤) (𝓝 (matrixScalarEntriesEquiv m 0)) at h
    simpa only [(matrixScalarEntriesEquiv m).apply_symm_apply, map_zero] using h
  have hzero : TendstoUniformly (fun L : ℝ ↦ fun z ↦ G L z - G0 z)
      (fun _ : PlanarHopfSphere C ↦
        (0 : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m)) atTop :=
    tendsto_prod_top_iff.mp hop
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h := Metric.tendstoUniformly_iff.mp hzero ε hε
  filter_upwards [h] with L hL z
  have hh : ‖G L z - G0 z‖ < ε := by simpa only [dist_zero_left] using hL z
  simpa only [dist_eq_norm, norm_sub_rev] using hh

/-- The same actual scalar Gram has a common positive quadratic lower bound and actual
inverse equivalences with a common norm bound at every sufficiently large scalar frequency.

Proof: the actual smooth positive limiting field has a common compact lower bound. Actual
uniform operator convergence preserves half that bound for all large frequencies and all
points. Native finite-dimensional coercivity produces actual units/equivalences, and the
actual anti-Lipschitz estimate bounds their actual inverse norms. Source: prop:matrix,(3.6). -/
theorem matrix_scalar_gram_uniform_inverse_bound
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (hrpos : ∀ w, planarOrbitCurvature planarHopfFlow f w ≠ 0 → 0 < r w)
    (hspan : ∀ z, ∀ b : EuclideanSpace ℝ (Fin m), b ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) ≠ 0 ∧
        0 < ⟪A (planarHopfFlow t z), b⟫) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ z : PlanarHopfSphere C,
      (∀ a : MatrixScalarCoefficients m, δ * ‖a‖ ^ 2 ≤
        ⟪matrixScalarGram A (planarOrbitCurvature planarHopfFlow f)
          (matrixScalarOscillatoryBase f ηb r L) z a, a⟫) ∧
      ∃ e : MatrixScalarCoefficients m ≃L[ℝ] MatrixScalarCoefficients m,
        e.toContinuousLinearMap = matrixScalarGram A (planarOrbitCurvature planarHopfFlow f)
          (matrixScalarOscillatoryBase f ηb r L) z ∧ ‖e.symm.toContinuousLinearMap‖ ≤ B := by
  let κ := planarOrbitCurvature planarHopfFlow f
  let G0 := matrixScalarGramLimit A κ ηb r
  obtain ⟨μ, hμ, hbound⟩ := compact_positive_operator_lower_bound
    (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C))) G0
    (matrix_scalar_gram_limit_contMDiff A hA κ ηb r hf.curvature_smooth hb hr).continuous.continuousOn
    (fun z _ a ha ↦ matrix_scalar_gram_limit_positive f hf A hA ηb r hb hr hrpos hspan z a ha)
  let δ : ℝ := μ / 2
  have hδ : 0 < δ := half_pos hμ
  refine ⟨δ, δ⁻¹, hδ, inv_pos.mpr hδ, ?_⟩
  have hconv := (Metric.tendstoUniformly_iff.mp
    (matrix_scalar_gram_tendsto_uniformly f hf A hA ηb r hb hr)) δ hδ
  filter_upwards [hconv] with L hL z
  let H := matrixScalarGram A κ (matrixScalarOscillatoryBase f ηb r L) z
  have hsmall : ‖H - G0 z‖ ≤ δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hL z).le
  have hcoercive (a : MatrixScalarCoefficients m) : δ * ‖a‖ ^ 2 ≤ ⟪H a, a⟫ := by
    have herr : |⟪(H - G0 z) a, a⟫| ≤ δ * ‖a‖ ^ 2 := by
      calc
        _ ≤ ‖(H - G0 z) a‖ * ‖a‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖H - G0 z‖ * ‖a‖) * ‖a‖ :=
          mul_le_mul_of_nonneg_right ((H - G0 z).le_opNorm a) (norm_nonneg _)
        _ ≤ (δ * ‖a‖) * ‖a‖ := by gcongr
        _ = δ * ‖a‖ ^ 2 := by ring
    have hsum : ⟪H a, a⟫ = ⟪G0 z a, a⟫ + ⟪(H - G0 z) a, a⟫ := by
      simp only [sub_apply, inner_sub_left]
      ring
    have hlo := hbound z (mem_univ _) a
    have he := (abs_le.mp herr).1
    rw [hsum]
    dsimp only [δ] at *
    linarith
  refine ⟨hcoercive, ?_⟩
  let c : ℝ≥0 := ⟨δ, hδ.le⟩
  have hc : 0 < c := hδ
  have hnorm (a : MatrixScalarCoefficients m) : ‖a‖ ^ 2 * c ≤ ‖⟪H a, a⟫‖ := by
    have hlo : ‖a‖ ^ 2 * (c : ℝ) ≤ ⟪H a, a⟫ := by
      change ‖a‖ ^ 2 * δ ≤ _
      simpa only [mul_comm] using hcoercive a
    exact hlo.trans (by simpa only [Real.norm_eq_abs] using le_abs_self ⟪H a, a⟫)
  have hanti := ContinuousLinearMap.antilipschitz_of_forall_le_inner_map H hc hnorm
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map H hc hnorm
  let e := ContinuousLinearEquiv.unitsEquiv ℝ (MatrixScalarCoefficients m) u
  have he : e.toContinuousLinearMap = H := by
    apply ContinuousLinearMap.ext
    intro a
    change (u : MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m) a = H a
    rw [hu]
  refine ⟨e, he, e.symm.toContinuousLinearMap.opNorm_le_bound (inv_nonneg.mpr hδ.le) ?_⟩
  intro a
  change ‖e.symm a‖ ≤ δ⁻¹ * ‖a‖
  have h := hanti.le_mul_dist (e.symm a) 0
  have hi : H (e.symm a) = a := by rw [← he]; exact e.apply_symm_apply a
  have hcδ : (c : ℝ) = δ := rfl
  simpa only [map_zero, dist_zero_right, NNReal.coe_inv, hcδ, hi] using h

#print axioms matrix_scalar_gram_limit_entry_cases
#print axioms matrix_scalar_gram_limit_quadratic_average
#print axioms matrix_scalar_gram_limit_quadratic
#print axioms matrix_scalar_gram_limit_contMDiff
#print axioms matrix_scalar_gram_limit_positive
#print axioms matrix_scalar_gram_tendsto_uniformly
#print axioms matrix_scalar_gram_uniform_inverse_bound

end Smooth
end GlobalEmbedding.Paper
