import GlobalEmbedding.Paper.MatrixNativeAngleResidual
import GlobalEmbedding.Paper.MatrixCompactPositiveOperatorBound
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The actual four-moment Gram limit on the native Hopf sphere

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, lines303–313.
DAG: `matrix-angle-gram-limit`. W1 exclusive actual limiting Gram and uniform inverse.
The original Euclidean coefficient space and literal shared Gram operator are retained.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace Matrix NNReal

namespace GlobalEmbedding.Paper

/-- Finite coordinates for actual Euclidean operators, retaining their actual operator norm.
Only the ordinary finite Pi norm is used on the temporary coordinate space; no Matrix
norm instance is introduced. -/
def matrixAngleEntriesEquiv : (Fin 4 → Fin 4 → ℝ) ≃L[ℝ]
    (MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients) :=
  ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) :
    (Fin 4 → Fin 4 → ℝ) ≃ₗ[ℝ]
      (MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients)).toContinuousLinearEquiv

/-- This coordinate equivalence has the literal matrix action on Euclidean vectors. -/
theorem matrixAngleEntriesEquiv_apply (A : Fin 4 → Fin 4 → ℝ)
    (v : MatrixAngleCoefficients) (i : Fin 4) :
    matrixAngleEntriesEquiv A v i = ∑ j, A i j * v j := rfl

/-- Actual operator entries are evaluations on the actual Euclidean standard basis. -/
theorem matrixAngleEntriesEquiv_symm_apply
    (L : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients) (i j : Fin 4) :
    matrixAngleEntriesEquiv.symm L i j = L (EuclideanSpace.single j 1) i := by
  have h := congrArg (fun A : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients ↦
    A (EuclideanSpace.single j 1) i) (matrixAngleEntriesEquiv.apply_symm_apply L)
  simpa only [matrixAngleEntriesEquiv_apply, PiLp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- The original fixed amplitudes whose sine/cosine factors form the four Gram rows. -/
def matrixAngleRowAmplitude {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (i : Fin 4) (z : PlanarHopfSphere C) : ℝ :=
  ![-1, matrixPlanarT f z, -matrixPlanarS f z, matrixPlanarB f z] i

/-- The genuine nonoscillatory limiting entries, in the original order 0,1,2,3.
The even-coordinate and odd-coordinate blocks are the two original weighted Grams. -/
def matrixAngleGramLimitEntries {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) : Fin 4 → Fin 4 → ℝ := fun i j ↦
  if i.val % 2 = j.val % 2 then (1 / 2 : ℝ) * orbitAverage planarHopfFlow
    (fun w ↦ matrixPlanarRho f w * matrixAngleRowAmplitude f i w *
      matrixAngleRowAmplitude f j w) z else 0

/-- The actual limiting Gram operator on the same Euclidean coefficient space. -/
def matrixAngleGramLimit {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients :=
  matrixAngleEntriesEquiv (matrixAngleGramLimitEntries f z)

/-- The actual shared weighted Gram operator has the literal weighted period entries.

Proof: the actual native smooth scalar data make the actual profile and its rank-one
operator continuous, hence genuinely period integrable. Apply the fixed continuous linear
functional evaluating the operator on a standard basis vector and projecting a coordinate
to commute with the actual integral. Its inner product with that basis vector is exactly
the corresponding actual profile coordinate. Source: prop:matrix, derivative Gram, line307. -/
theorem matrix_angle_gram_entries {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (T : ℝ) (z : PlanarHopfSphere C) (i j : Fin 4) :
    matrixAngleEntriesEquiv.symm
      (matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z) i j =
      orbitAverage planarHopfFlow (fun w ↦ matrixPlanarRho f w *
        matrixAngleBaseProfile f T w i * matrixAngleBaseProfile f T w j) z := by
  obtain ⟨hs, ht, hb, hρ⟩ := matrix_planar_data_contMDiff f hf
  have hF : Continuous (matrixAngleBaseProfile f T) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp
    apply continuous_pi
    intro k
    fin_cases k
    · exact (Real.continuous_sin.comp (continuous_const.mul ht.continuous)).neg
    · exact ht.continuous.mul
        (Real.continuous_cos.comp (continuous_const.mul ht.continuous))
    · exact hs.continuous.neg.mul
        (Real.continuous_sin.comp (continuous_const.mul ht.continuous))
    · exact hb.continuous.mul
        (Real.continuous_cos.comp (continuous_const.mul ht.continuous))
  let F : PlanarHopfSphere C → MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients :=
    fun w ↦ matrixPlanarRho f w •
      (ContinuousLinearMap.toSpanSingleton ℝ (matrixAngleBaseProfile f T w)).comp
        (InnerProductSpace.toDual ℝ MatrixAngleCoefficients (matrixAngleBaseProfile f T w))
  have hFc : Continuous F := hρ.continuous.smul
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ MatrixAngleCoefficients).continuous.comp hF).clm_comp
      ((InnerProductSpace.toDual ℝ MatrixAngleCoefficients).continuous.comp hF))
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  let L : (MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) i).comp
      (ContinuousLinearMap.apply ℝ MatrixAngleCoefficients (EuclideanSpace.single j 1))
  rw [matrixAngleEntriesEquiv_symm_apply]
  change L (orbitAverage planarHopfFlow F z) = _
  change L (∫ t in (0 : ℝ)..1, F (planarHopfFlow t z)) = _
  have hint : IntegrableOn (fun t : ℝ ↦ F (planarHopfFlow t z)) (Icc (0 : ℝ) 1) :=
    (hFc.comp hflow).continuousOn.integrableOn_Icc
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← L.integral_comp_comm hint]
  change _ = ∫ t in (0 : ℝ)..1, matrixPlanarRho f (planarHopfFlow t z) *
    matrixAngleBaseProfile f T (planarHopfFlow t z) i *
    matrixAngleBaseProfile f T (planarHopfFlow t z) j
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp [L, F, EuclideanSpace.inner_single_right]
  ring

/-- The fixed scalar phases representing the literal sine and cosine rows. -/
def matrixAngleRowPhase (i : Fin 4) : ℝ :=
  ![-(Real.pi / 2), 0, -(Real.pi / 2), 0] i

/-- Every actual profile row is its fixed amplitude times the indicated phase cosine. -/
theorem matrixAngleBaseProfile_row {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (T : ℝ) (z : PlanarHopfSphere C) (i : Fin 4) :
    matrixAngleBaseProfile f T z i = matrixAngleRowAmplitude f i z *
      Real.cos (T * matrixPlanarT f z + matrixAngleRowPhase i) := by
  fin_cases i <;>
    simp [matrixAngleBaseProfile, matrixAngleMomentDirection, matrixAngleRowAmplitude,
      matrixAngleRowPhase, matrixPlanarS, matrixPlanarT, matrixPlanarB,
      ← sub_eq_add_neg, Real.cos_sub_pi_div_two]

/-- The cosine of the fixed phase difference is exactly the same-block indicator. -/
theorem matrixAngleRowPhase_cos_sub (i j : Fin 4) :
    Real.cos (matrixAngleRowPhase i - matrixAngleRowPhase j) =
      if i.val % 2 = j.val % 2 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [matrixAngleRowPhase, Real.cos_neg, Real.cos_pi_div_two]

/-- The exact actual Gram entry is its limiting entry plus a true frequency-2T average.

Proof: write each actual row as its amplitude times its fixed phase cosine. Native
2cos(x)cos(y)=cos(x-y)+cos(x+y) gives the integrand identity. The actual amplitudes and
phase profiles are continuous, so both actual summands are integrable and integral
linearity is justified. The phase-difference cosine is exactly the block indicator.
Source: prop:matrix, sine/cosine product Gram limit, lines305–307. -/
theorem matrix_angle_gram_entry_decomposition {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (T : ℝ) (z : PlanarHopfSphere C) (i j : Fin 4) :
    matrixAngleEntriesEquiv.symm
      (matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z) i j =
      matrixAngleGramLimitEntries f z i j + (1 / 2 : ℝ) * orbitAverage planarHopfFlow
        (fun w ↦ (matrixPlanarRho f w * matrixAngleRowAmplitude f i w *
          matrixAngleRowAmplitude f j w) * Real.cos ((2 * T) * matrixPlanarT f w +
            (matrixAngleRowPhase i + matrixAngleRowPhase j))) z := by
  obtain ⟨hs, ht, hb, hρ⟩ := matrix_planar_data_contMDiff f hf
  have hA (k : Fin 4) : Continuous (matrixAngleRowAmplitude f k) := by
    fin_cases k
    · exact continuous_const
    · exact ht.continuous
    · exact hs.continuous.neg
    · exact hb.continuous
  let a : PlanarHopfSphere C → ℝ := fun w ↦ matrixPlanarRho f w *
    matrixAngleRowAmplitude f i w * matrixAngleRowAmplitude f j w
  have ha : Continuous a := (hρ.continuous.mul (hA i)).mul (hA j)
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have htrig (w : PlanarHopfSphere C) :
      matrixPlanarRho f w * matrixAngleBaseProfile f T w i *
        matrixAngleBaseProfile f T w j =
      (1 / 2 : ℝ) * (a w * Real.cos (matrixAngleRowPhase i - matrixAngleRowPhase j)) +
      (1 / 2 : ℝ) * (a w * Real.cos ((2 * T) * matrixPlanarT f w +
        (matrixAngleRowPhase i + matrixAngleRowPhase j))) := by
    rw [matrixAngleBaseProfile_row, matrixAngleBaseProfile_row]
    have hh := Real.two_mul_cos_mul_cos
      (T * matrixPlanarT f w + matrixAngleRowPhase i)
      (T * matrixPlanarT f w + matrixAngleRowPhase j)
    have hsub : (T * matrixPlanarT f w + matrixAngleRowPhase i) -
        (T * matrixPlanarT f w + matrixAngleRowPhase j) =
        matrixAngleRowPhase i - matrixAngleRowPhase j := by ring
    have hadd : (T * matrixPlanarT f w + matrixAngleRowPhase i) +
        (T * matrixPlanarT f w + matrixAngleRowPhase j) =
        (2 * T) * matrixPlanarT f w +
          (matrixAngleRowPhase i + matrixAngleRowPhase j) := by ring
    rw [hsub, hadd] at hh
    calc
      _ = (a w / 2) * (2 *
          Real.cos (T * matrixPlanarT f w + matrixAngleRowPhase i) *
          Real.cos (T * matrixPlanarT f w + matrixAngleRowPhase j)) := by dsimp [a]; ring
      _ = _ := by rw [hh]; ring
  have hc : Continuous (fun t : ℝ ↦ Real.cos ((2 * T) *
      matrixPlanarT f (planarHopfFlow t z) +
      (matrixAngleRowPhase i + matrixAngleRowPhase j))) :=
    Real.continuous_cos.comp ((continuous_const.mul (ht.continuous.comp hflow)).add
      continuous_const)
  rw [matrix_angle_gram_entries f hf T z i j]
  change (∫ t in (0 : ℝ)..1, _) = _
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  conv_lhs => arg 2; ext t; dsimp only; rw [htrig]
  have hi1 : IntegrableOn (fun t : ℝ ↦ (1 / 2 : ℝ) *
      (a (planarHopfFlow t z) * Real.cos (matrixAngleRowPhase i - matrixAngleRowPhase j)))
      (Icc (0 : ℝ) 1) :=
    (continuous_const.mul ((ha.comp hflow).mul continuous_const)).continuousOn.integrableOn_Icc
  have hi2 : IntegrableOn (fun t : ℝ ↦ (1 / 2 : ℝ) *
      (a (planarHopfFlow t z) * Real.cos ((2 * T) * matrixPlanarT f (planarHopfFlow t z) +
        (matrixAngleRowPhase i + matrixAngleRowPhase j)))) (Icc (0 : ℝ) 1) :=
    (continuous_const.mul ((ha.comp hflow).mul hc)).continuousOn.integrableOn_Icc
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, integral_mul_const]
  have hlim : (1 / 2 : ℝ) *
      ((∫ t in Icc (0 : ℝ) 1, a (planarHopfFlow t z)) *
        Real.cos (matrixAngleRowPhase i - matrixAngleRowPhase j)) =
      matrixAngleGramLimitEntries f z i j := by
    rw [matrixAngleRowPhase_cos_sub]
    dsimp only [matrixAngleGramLimitEntries, orbitAverage]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    split_ifs <;> simp_all only [a, mul_one, mul_zero]
  rw [hlim]
  congr 1
  change _ = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, _
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

/-- The literal four-by-four Gram converges uniformly in the actual Euclidean operator
norm to its two-block weighted Gram limit on the whole actual Hopf sphere.

Proof: the exact entry decomposition expresses every error as one half an actual smooth
amplitude frequency-2T oscillatory average. The accepted finite-family theorem supplies
one common threshold for all sixteen entries. The finite coordinate norm bounds their
matrix difference. The fixed continuous linear coordinate equivalence transfers this
bound to the original Euclidean operator norm. Source: prop:matrix, line307. -/
theorem matrix_angle_gram_tendsto_uniformly {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ) :
    TendstoUniformly
      (fun T : ℝ ↦ matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T)
      (matrixAngleGramLimit f) atTop := by
  obtain ⟨hs, ht, hb, hρ⟩ := matrix_planar_data_contMDiff f hf
  have hA (k : Fin 4) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (matrixAngleRowAmplitude f k) := by
    fin_cases k
    · exact contMDiff_const
    · exact ht
    · exact hs.neg
    · exact hb
  let a : (Fin 4 × Fin 4) → PlanarHopfSphere C → ℝ := fun k w ↦
    matrixPlanarRho f w * matrixAngleRowAmplitude f k.1 w * matrixAngleRowAmplitude f k.2 w
  have ha (k : Fin 4 × Fin 4) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (a k) :=
    (hρ.mul (hA k.1)).mul (hA k.2)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let B : ℝ := ‖matrixAngleEntriesEquiv.toContinuousLinearMap‖
  have hB : 0 ≤ B := norm_nonneg matrixAngleEntriesEquiv.toContinuousLinearMap
  let δ : ℝ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall := matrix_hopf_finite_oscillatory_average f hf hunit hana a ha
    (fun _ ↦ 2) (fun k ↦ matrixAngleRowPhase k.1 + matrixAngleRowPhase k.2)
    (fun _ ↦ by norm_num) δ hδ
  filter_upwards [hsmall] with T hT z
  let G := matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z
  let D : Fin 4 → Fin 4 → ℝ :=
    matrixAngleEntriesEquiv.symm G - matrixAngleGramLimitEntries f z
  have hD (i j : Fin 4) : |D i j| ≤ δ := by
    have hd := matrix_angle_gram_entry_decomposition f hf T z i j
    have he : D i j = (1 / 2 : ℝ) * orbitAverage planarHopfFlow
        (fun w ↦ a (i, j) w * Real.cos ((2 * T) * matrixPlanarT f w +
          (matrixAngleRowPhase i + matrixAngleRowPhase j))) z := by
      dsimp only [D, G, Pi.sub_apply]
      rw [hd]
      ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hh := hT (i, j) z
    nlinarith [abs_nonneg (orbitAverage planarHopfFlow
      (fun w ↦ a (i, j) w * Real.cos ((2 * T) * matrixPlanarT f w +
        (matrixAngleRowPhase i + matrixAngleRowPhase j))) z)]
  have hnorm : ‖D‖ ≤ δ :=
    (pi_norm_le_iff_of_nonneg hδ.le).mpr fun i ↦
      (pi_norm_le_iff_of_nonneg hδ.le).mpr fun j ↦ by
        simpa only [Real.norm_eq_abs] using hD i j
  have heq : G - matrixAngleGramLimit f z = matrixAngleEntriesEquiv D := by
    dsimp only [D, matrixAngleGramLimit]
    rw [map_sub, matrixAngleEntriesEquiv.apply_symm_apply]
  rw [dist_eq_norm, norm_sub_rev]
  change ‖G - matrixAngleGramLimit f z‖ < ε
  rw [heq]
  calc
    _ ≤ B * ‖D‖ := matrixAngleEntriesEquiv.toContinuousLinearMap.le_opNorm D
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hnorm hB
    _ < (B + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp only [δ]; field_simp

/-- The actual limiting operator is positive on every nonzero Euclidean coefficient vector.

Proof: its quadratic form is half the sum of the two actual weighted-period Gram forms,
with coefficient pairs (v0,v2) and (v1,v3). Both forms are nonnegative by their actual
positive definiteness, and at least one coefficient pair is nonzero. Source: prop:matrix,
actual positive limiting weighted blocks, line307. -/
theorem matrix_angle_gram_limit_positive {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (z : PlanarHopfSphere C) (v : MatrixAngleCoefficients) (hv : v ≠ 0) :
    0 < ⟪matrixAngleGramLimit f z v, v⟫ := by
  let Gs : Matrix (Fin 2) (Fin 2) ℝ := fun i j ↦ ∫ t in Icc (0 : ℝ) 1,
    matrixPlanarRho f (planarHopfFlow t z) *
      ![1, matrixPlanarS f (planarHopfFlow t z)] i *
      ![1, matrixPlanarS f (planarHopfFlow t z)] j
  let Gc : Matrix (Fin 2) (Fin 2) ℝ := fun i j ↦ ∫ t in Icc (0 : ℝ) 1,
    matrixPlanarRho f (planarHopfFlow t z) *
      ![matrixPlanarT f (planarHopfFlow t z), matrixPlanarB f (planarHopfFlow t z)] i *
      ![matrixPlanarT f (planarHopfFlow t z), matrixPlanarB f (planarHopfFlow t z)] j
  obtain ⟨hGs, hGc⟩ := matrix_native_weighted_gram_blocks f hf hunit hana z
  let u : Fin 2 → ℝ := ![v 0, v 2]
  let w : Fin 2 → ℝ := ![v 1, v 3]
  have hq : ⟪matrixAngleGramLimit f z v, v⟫ =
      (1 / 2 : ℝ) * (star u ⬝ᵥ (Gs *ᵥ u)) +
      (1 / 2 : ℝ) * (star w ⬝ᵥ (Gc *ᵥ w)) := by
    simp [matrixAngleGramLimit, matrixAngleEntriesEquiv_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ, matrixAngleGramLimitEntries, matrixAngleRowAmplitude,
      orbitAverage, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc, Gs, Gc, u, w]
    ring
  have hsn : 0 ≤ star u ⬝ᵥ (Gs *ᵥ u) := hGs.posSemidef.dotProduct_mulVec_nonneg u
  have hcn : 0 ≤ star w ⬝ᵥ (Gc *ᵥ w) := hGc.posSemidef.dotProduct_mulVec_nonneg w
  rw [hq]
  by_cases hu : u = 0
  · have hw : w ≠ 0 := by
      intro hw
      apply hv
      ext i
      have h0 := congrFun hu 0
      have h2 := congrFun hu 1
      have h1 := congrFun hw 0
      have h3 := congrFun hw 1
      fin_cases i <;> simp_all [u, w]
    have hpos := hGc.dotProduct_mulVec_pos hw
    linarith
  · have hpos := hGs.dotProduct_mulVec_pos hu
    linarith

/-- The actual limiting weighted Gram field is continuous on the whole native sphere.

Proof: every fixed row amplitude and the actual cutoff are native smooth. The accepted
actual native Hopf averaging theorem makes each actual moment smooth, hence continuous.
Each limiting entry is a fixed scalar multiple or zero; the fixed operator coordinate
equivalence preserves continuity. Source: prop:matrix, compact uniform positivity, line307. -/
theorem matrix_angle_gram_limit_continuous {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    Continuous (matrixAngleGramLimit f) := by
  obtain ⟨hs, ht, hb, hρ⟩ := matrix_planar_data_contMDiff f hf
  have hA (k : Fin 4) : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (matrixAngleRowAmplitude f k) := by
    fin_cases k
    · exact contMDiff_const
    · exact ht
    · exact hs.neg
    · exact hb
  have hc : Continuous (fun z : PlanarHopfSphere C ↦
      (matrixAngleGramLimitEntries f z : Fin 4 → Fin 4 → ℝ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i.val % 2 = j.val % 2
    · simp only [matrixAngleGramLimitEntries, h, ite_true]
      exact continuous_const.mul (planarHopfAverage_contMDiff _
        ((hρ.mul (hA i)).mul (hA j))).continuous
    · simp only [matrixAngleGramLimitEntries, h, ite_false]
      exact continuous_const
  exact matrixAngleEntriesEquiv.continuous.comp hc

/-- The actual four-by-four Gram has a common positive quadratic lower bound and actual
inverse equivalences with one common operator-norm bound at every sufficiently large
frequency, uniformly over the whole native Hopf sphere.

Proof: apply the accepted compact-positive-operator theorem to the actual continuous
positive limiting Gram to obtain its common lower bound mu. Uniform operator convergence
makes every large-frequency perturbation smaller than mu/2; the actual inner-product norm
estimate preserves the lower bound mu/2. Native finite-dimensional coercivity gives an
actual unit/equivalence. Its actual anti-Lipschitz estimate evaluated on the inverse bounds
its operator norm by (mu/2)^-1. Source: prop:matrix, uniform inverse, line307. -/
theorem matrix_angle_gram_uniform_inverse_bound {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ᶠ T : ℝ in atTop, ∀ z : PlanarHopfSphere C,
      (∀ v : MatrixAngleCoefficients, δ * ‖v‖ ^ 2 ≤
        ⟪matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z v, v⟫) ∧
      ∃ e : MatrixAngleCoefficients ≃L[ℝ] MatrixAngleCoefficients,
        e.toContinuousLinearMap = matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ L := by
  obtain ⟨μ, hμ, hbound⟩ := compact_positive_operator_lower_bound
    (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    (matrixAngleGramLimit f) (matrix_angle_gram_limit_continuous f hf).continuousOn
    (fun z _ v hv ↦ matrix_angle_gram_limit_positive f hf hunit hana z v hv)
  let δ : ℝ := μ / 2
  have hδ : 0 < δ := half_pos hμ
  refine ⟨δ, δ⁻¹, hδ, inv_pos.mpr hδ, ?_⟩
  have hconv := (Metric.tendstoUniformly_iff.mp
    (matrix_angle_gram_tendsto_uniformly f hf hunit hana)) δ hδ
  filter_upwards [hconv] with T hT z
  let A := matrixAngleGram f (planarOrbitCurvature planarHopfFlow f) T z
  have hsmall : ‖A - matrixAngleGramLimit f z‖ ≤ δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hT z).le
  have hcoercive (v : MatrixAngleCoefficients) : δ * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
    have herr : |⟪(A - matrixAngleGramLimit f z) v, v⟫| ≤ δ * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖(A - matrixAngleGramLimit f z) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A - matrixAngleGramLimit f z‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            ((A - matrixAngleGramLimit f z).le_opNorm v) (norm_nonneg _)
        _ ≤ (δ * ‖v‖) * ‖v‖ := by gcongr
        _ = δ * ‖v‖ ^ 2 := by ring
    have hsum : ⟪A v, v⟫ = ⟪matrixAngleGramLimit f z v, v⟫ +
        ⟪(A - matrixAngleGramLimit f z) v, v⟫ := by
      simp only [sub_apply, inner_sub_left]
      ring
    have hlo := hbound z (mem_univ _) v
    rw [hsum]
    have he := (abs_le.mp herr).1
    dsimp only [δ] at *
    linarith
  refine ⟨hcoercive, ?_⟩
  let c : ℝ≥0 := ⟨δ, hδ.le⟩
  have hc : 0 < c := hδ
  have hnorm (v : MatrixAngleCoefficients) : ‖v‖ ^ 2 * c ≤ ‖⟪A v, v⟫‖ := by
    have hlo : ‖v‖ ^ 2 * (c : ℝ) ≤ ⟪A v, v⟫ := by
      change ‖v‖ ^ 2 * δ ≤ _
      simpa only [mul_comm] using hcoercive v
    exact hlo.trans (by simpa only [Real.norm_eq_abs] using le_abs_self ⟪A v, v⟫)
  have hanti := ContinuousLinearMap.antilipschitz_of_forall_le_inner_map A hc hnorm
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map A hc hnorm
  let e := ContinuousLinearEquiv.unitsEquiv ℝ MatrixAngleCoefficients u
  have he : e.toContinuousLinearMap = A := by
    apply ContinuousLinearMap.ext
    intro v
    change (u : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients) v = A v
    rw [hu]
  refine ⟨e, he, e.symm.toContinuousLinearMap.opNorm_le_bound (inv_nonneg.mpr hδ.le) ?_⟩
  intro v
  change ‖e.symm v‖ ≤ δ⁻¹ * ‖v‖
  have h := hanti.le_mul_dist (e.symm v) 0
  have hi : A (e.symm v) = v := by rw [← he]; exact e.apply_symm_apply v
  have hcδ : (c : ℝ) = δ := rfl
  simpa only [map_zero, dist_zero_right, NNReal.coe_inv, hcδ, hi] using h

#print axioms matrix_angle_gram_tendsto_uniformly
#print axioms matrix_angle_gram_limit_positive
#print axioms matrix_angle_gram_limit_continuous
#print axioms matrix_angle_gram_uniform_inverse_bound

end GlobalEmbedding.Paper
