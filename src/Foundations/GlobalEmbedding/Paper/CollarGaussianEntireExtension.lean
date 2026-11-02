import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Entire extension of a compactly supported Gaussian convolution

For a fixed positive Gaussian width, extend the real kernel by replacing each real coordinate
difference by the corresponding complex coordinate difference and using the complex exponential.
The real-valued input is embedded coordinatewise into the complex Euclidean target. Since the
input has compact support, differentiation under the integral is justified on each compact
parameter neighborhood by a uniform bound for the complex derivative of the kernel.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar` proof,
line 520.
-/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The complex Gaussian convolution of a smooth compactly supported real map is entire.

The Gaussian normalization is `(π ε)^(-d/2)` and the complex target map is formed by embedding
each real coordinate of `f y` into `ℂ`. In the exponent we use the sum of the squares of the
complex coordinate differences, without complex conjugation; this is the entire extension of the
real Gaussian exponent. The integral is written in product coordinates `Fin d → ℝ`, with the
standard `PiLp` coordinate equivalence identifying this with real Euclidean space and its
Lebesgue measure. It may be taken over the whole space because `f` has compact support. Its proof
differentiates the integrand in the complex parameter and uses compact support to obtain a locally
uniform integrable bound, as in the source.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar` proof,
line 520.
-/
theorem collar_gaussian_entire_extension {d N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N))
    (_hf : ContDiff ℝ ∞ f) (_hcompact : HasCompactSupport f) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin d) =>
      ∫ y : Fin d → ℝ,
        ((((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp
            (-((∑ i : Fin d,
              ((EuclideanSpace.equiv (Fin d) ℂ z) i -
                (y i : ℂ)) ^ 2)) / (ε : ℂ))) •
          (EuclideanSpace.equiv (Fin N) ℂ).symm
            (fun j : Fin N =>
              ((EuclideanSpace.equiv (Fin N) ℝ
                (f ((EuclideanSpace.equiv (Fin d) ℝ).symm y))) j : ℂ))) := by
  let Z := EuclideanSpace ℂ (Fin d)
  let W := EuclideanSpace ℂ (Fin N)
  let cy : (Fin d → ℝ) → Z := fun y ↦
    (EuclideanSpace.equiv (Fin d) ℂ).symm (fun i ↦ (y i : ℂ))
  let cf : (Fin d → ℝ) → W := fun y ↦
    (EuclideanSpace.equiv (Fin N) ℂ).symm (fun j ↦
      ((EuclideanSpace.equiv (Fin N) ℝ
        (f ((EuclideanSpace.equiv (Fin d) ℝ).symm y))) j : ℂ))
  let k : Z × Z → ℂ := fun p ↦
    (((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp (-(∑ i : Fin d, (p.1 i - p.2 i) ^ 2) / (ε : ℂ))
  have hk : ContDiff ℂ ⊤ k := by
    apply contDiff_const.mul
    apply ContDiff.cexp
    apply ContDiff.div_const
    apply ContDiff.neg
    apply ContDiff.sum
    intro i hi
    exact (((EuclideanSpace.proj (𝕜 := ℂ) i).contDiff.comp contDiff_fst).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) i).contDiff.comp contDiff_snd)).pow 2
  have hcy : Continuous cy := by
    exact (EuclideanSpace.equiv (Fin d) ℂ).symm.continuous.comp
      (continuous_pi fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i))
  have hcf : Continuous cf := by
    apply (EuclideanSpace.equiv (Fin N) ℂ).symm.continuous.comp
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp ((continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin N) ℝ).continuous.comp
        (_hf.continuous.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous)))
  have hcompact : HasCompactSupport cf := by
    let c : EuclideanSpace ℝ (Fin N) → W := fun v ↦
      (EuclideanSpace.equiv (Fin N) ℂ).symm
        (fun j ↦ ((EuclideanSpace.equiv (Fin N) ℝ v) j : ℂ))
    have hc : c 0 = 0 := by
      apply (EuclideanSpace.equiv (Fin N) ℂ).injective
      ext j
      simp [c]
    exact (_hcompact.comp_homeomorph
      (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph).comp_left hc
  let F : Z → (Fin d → ℝ) → W := fun z y ↦ k (z, cy y) • cf y
  let D : Z → (Fin d → ℝ) → Z →L[ℂ] W := fun z y ↦
    ((fderiv ℂ k (z, cy y)).comp (ContinuousLinearMap.inl ℂ Z Z)).smulRight (cf y)
  have hF : Continuous (fun p : Z × (Fin d → ℝ) ↦ F p.1 p.2) :=
    (hk.continuous.comp (continuous_fst.prodMk (hcy.comp continuous_snd))).smul
      (hcf.comp continuous_snd)
  have hD : Continuous (fun p : Z × (Fin d → ℝ) ↦ D p.1 p.2) := by
    exact (ContinuousLinearMap.smulRightL ℂ Z W).continuous₂.comp₂
      (((hk.continuous_fderiv (by simp)).comp
        (continuous_fst.prodMk (hcy.comp continuous_snd))).clm_comp_const _)
      (hcf.comp continuous_snd)
  have hderiv (z : Z) (y : Fin d → ℝ) : HasFDerivAt (F · y) (D z y) z := by
    exact (((hk.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
      (hasFDerivAt_prodMk_left z (cy y))).smul_const (cf y)
  change Differentiable ℂ (fun z ↦ ∫ y, F z y)
  intro z₀
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod hcompact).exists_bound_of_continuousOn
    hD.continuousOn
  have hFi (z : Z) : Integrable (F z) := by
    have hcF : HasCompactSupport (F z) := by
      apply HasCompactSupport.intro hcompact
      intro y hy
      change k (z, cy y) • cf y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, smul_zero]
    exact (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hcF
  apply (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := D) (bound := (tsupport cf).indicator (fun _ ↦ C))
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Filter.Eventually.of_forall fun z ↦ (hFi z).aestronglyMeasurable)
    (hFi z₀)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ?_ ?_ ?_).differentiableAt
  · filter_upwards with y z hz
    by_cases hy : y ∈ tsupport cf
    · rw [Set.indicator_of_mem hy]
      exact hC (z, y) ⟨Metric.ball_subset_closedBall hz, hy⟩
    · rw [Set.indicator_of_notMem hy]
      simp [D, image_eq_zero_of_notMem_tsupport hy]
  · rw [integrable_indicator_iff (isClosed_tsupport cf).measurableSet]
    exact integrableOn_const hcompact.measure_ne_top
  · exact Filter.Eventually.of_forall fun y z _ ↦ hderiv z y

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_gaussian_entire_extension
