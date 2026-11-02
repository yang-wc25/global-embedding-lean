import Initialization.Colored.FirstDerivative
import Initialization.Colored.LocalGerms
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# First-jet comparison for the actual native colored sphere arguments

The comparison is between the derivative of the literal Euclidean map and the
actual Hopf velocity with one common covector. Same-color support disjointness
removes any dependence on the number of patches, and the sole finite factor
comes from the palette fixed before K,T.
-/

noncomputable section
open Function Set Metric Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every member of an actual square partition has absolute value at most one. -/
theorem coloredCutoff_abs_le_one (χ : ι → E → ℝ)
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (x : E) (i : ι) : |χ i x| ≤ 1 := by
  have hsq : χ i x ^ 2 ≤ 1 := by
    rw [← hsquare x]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (χ j x)) (Finset.mem_univ i)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The actual color coordinate is differentiable even when each unsupported
phase has arbitrary values outside its own support. -/
theorem coloredCoordinate_differentiableAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (c : Fin C) (x : E)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ i) x) :
    DifferentiableAt ℝ (coloredCoordinate color χ ℓ T c) x := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ x ∈ tsupport (χ i)
  · obtain ⟨i, hic, hxi⟩ := hactive
    subst c
    exact ((coloredWave_hasFDerivAt (χ i) (ℓ i) _ _ T x
      (hχ i).hasFDerivAt (hℓ i hxi).hasFDerivAt).differentiableAt).congr_of_eventuallyEq
        (coloredCoordinate_eventually_single color χ ℓ hdisjoint T x i hxi)
  · have hx : ∀ i, color i = c → x ∉ tsupport (χ i) := by
      intro i hic hxi
      exact hactive ⟨i, hic, hxi⟩
    exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
      (coloredCoordinate_eventually_zero color χ ℓ T c x hx)

/-- The first-jet error of one actual color coordinate has no patch-count
factor. The right side consists exactly of cutoff and common-rate errors. -/
theorem coloredCoordinate_first_error_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (T A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (c : Fin C) (x v : E)
    (r : E →L[ℝ] ℝ)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ i) x)
    (hcutoff : ∀ i, x ∈ tsupport (χ i) → ‖fderiv ℝ (χ i) x‖ ≤ A)
    (hrate : ∀ i, x ∈ tsupport (χ i) → ‖T • fderiv ℝ (ℓ i) x - r‖ ≤ D) :
    ‖fderiv ℝ (coloredCoordinate color χ ℓ T c) x v -
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        coloredCoordinate color χ ℓ T c x * (r v : ℂ)‖ ≤
      (A + 2 * Real.pi * D) * ‖v‖ := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ x ∈ tsupport (χ i)
  · obtain ⟨i, hic, hxi⟩ := hactive
    subst c
    have hg := coloredCoordinate_eventually_single color χ ℓ hdisjoint T x i hxi
    rw [hg.fderiv_eq, hg.self_of_nhds]
    have hidentity :
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * coloredWave (χ i) (ℓ i) T x * (r v : ℂ) =
        χ i x • (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (Circle.exp (2 * Real.pi * T * ℓ i x) : ℂ) * (r v : ℂ)) := by
      simp only [coloredWave, RCLike.real_smul_eq_coe_mul]
      ring
    rw [hidentity]
    have he := coloredWave_first_error_bound (χ i) (ℓ i)
      (fderiv ℝ (χ i) x) (fderiv ℝ (ℓ i) x) r T x v
      (hχ i).hasFDerivAt (hℓ i hxi).hasFDerivAt
    have hdχ : |fderiv ℝ (χ i) x v| ≤ A * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hcutoff i hxi) (norm_nonneg v))
    have hdr : |T * fderiv ℝ (ℓ i) x v - r v| ≤ D * ‖v‖ := by
      have h := (T • fderiv ℝ (ℓ i) x - r).le_opNorm v
      exact h.trans (mul_le_mul_of_nonneg_right (hrate i hxi) (norm_nonneg v))
    have hunit := coloredCutoff_abs_le_one χ hsquare x i
    calc
      _ ≤ |fderiv ℝ (χ i) x v| + |χ i x| * (2 * Real.pi) *
          |T * fderiv ℝ (ℓ i) x v - r v| := he
      _ ≤ A * ‖v‖ + 1 * (2 * Real.pi) * (D * ‖v‖) := by gcongr
      _ = _ := by ring
  · have hx : ∀ i, color i = c → x ∉ tsupport (χ i) := by
      intro i hic hxi
      exact hactive ⟨i, hic, hxi⟩
    have hg := coloredCoordinate_eventually_zero color χ ℓ T c x hx
    rw [hg.fderiv_eq, hg.self_of_nhds]
    simp only [fderiv_zero, zero_apply, Pi.zero_apply,
      mul_zero, zero_mul, sub_zero, norm_zero]
    positivity

/-- A conservative L² coordinate bound with a palette-only factor. The empty
palette is included; the original palette always has at least two colors. -/
theorem complexEuclidean_norm_le_coordinate_bound {C : ℕ} (z : PlanarHopfAmbient C)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ c, ‖z c‖ ≤ B) :
    ‖z‖ ≤ ((C : ℝ) + 1) * B := by
  have hsq : ‖z‖ ^ 2 ≤ (C : ℝ) * B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin C, B ^ 2 := Finset.sum_le_sum (fun c _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hz c) 2)
      _ = _ := by simp
  have hC : 0 ≤ (C : ℝ) := by positivity
  have hCC : (C : ℝ) ≤ ((C : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (C : ℝ)]
  have hsq' := hsq.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg B))
  nlinarith [norm_nonneg z, mul_nonneg (by positivity : 0 ≤ (C : ℝ) + 1) hB]

/-- The literal native ambient color vector is differentiable. -/
theorem coloredAmbient_differentiableAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (x : E)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ i) x) :
    DifferentiableAt ℝ (coloredAmbient color χ ℓ T) x := by
  have hp : DifferentiableAt ℝ (fun y c ↦ coloredCoordinate color χ ℓ T c y) x :=
    differentiableAt_pi.mpr
      (fun c ↦ coloredCoordinate_differentiableAt color χ ℓ hdisjoint T c x hχ hℓ)
  have hto : ContDiff ℝ ∞ (WithLp.toLp 2 : (Fin C → ℂ) → PlanarHopfAmbient C) :=
    PiLp.contDiff_toLp
  exact (hto.contDiffAt.differentiableAt (by simp)).comp x hp

/-- The actual ambient Fréchet derivative has precisely the actual scalar
coordinate derivatives. -/
theorem coloredAmbient_fderiv_coordinate {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ) (T : ℝ) (x v : E)
    (h : DifferentiableAt ℝ (coloredAmbient color χ ℓ T) x) (c : Fin C) :
    (fderiv ℝ (coloredAmbient color χ ℓ T) x v) c =
      fderiv ℝ (coloredCoordinate color χ ℓ T c) x v := by
  let p : PlanarHopfAmbient C →L[ℝ] ℂ := (EuclideanSpace.proj c).restrictScalars ℝ
  have hp := p.hasFDerivAt.comp x h.hasFDerivAt
  have heq : p ∘ coloredAmbient color χ ℓ T = coloredCoordinate color χ ℓ T c := rfl
  rw [heq] at hp
  exact (congrArg (fun L : E →L[ℝ] ℂ ↦ L v) hp.fderiv).symm

/-- The ideal first derivative in one sphere factor is its actual Hopf velocity
multiplied by the common covector. -/
def coloredIdealAmbientDerivative {C : ℕ} (z : PlanarHopfAmbient C)
    (r : E →L[ℝ] ℝ) : E →L[ℝ] PlanarHopfAmbient C :=
  r.smulRight ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • z)

/-- Operator-norm control for the true ambient first jet, with a fixed
palette factor and no dependence on the number of patches. -/
theorem coloredAmbient_first_error_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (T A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (x : E)
    (r : E →L[ℝ] ℝ)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ i) x)
    (hcutoff : ∀ i, x ∈ tsupport (χ i) → ‖fderiv ℝ (χ i) x‖ ≤ A)
    (hrate : ∀ i, x ∈ tsupport (χ i) → ‖T • fderiv ℝ (ℓ i) x - r‖ ≤ D) :
    ‖fderiv ℝ (coloredAmbient color χ ℓ T) x -
      coloredIdealAmbientDerivative (coloredAmbient color χ ℓ T x) r‖ ≤
      ((C : ℝ) + 1) * (A + 2 * Real.pi * D) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hd := coloredAmbient_differentiableAt color χ ℓ hdisjoint T x hχ hℓ
  have hv : ‖(fderiv ℝ (coloredAmbient color χ ℓ T) x -
      coloredIdealAmbientDerivative (coloredAmbient color χ ℓ T x) r) v‖ ≤
      ((C : ℝ) + 1) * ((A + 2 * Real.pi * D) * ‖v‖) := by
    apply complexEuclidean_norm_le_coordinate_bound _ _ (by positivity)
    intro c
    have h := coloredCoordinate_first_error_bound color χ ℓ hdisjoint hsquare
      T A D hA hD c x v r hχ hℓ hcutoff hrate
    convert h using 1 <;>
      simp only [sub_apply, coloredIdealAmbientDerivative,
        ContinuousLinearMap.smulRight_apply, PiLp.sub_apply, PiLp.smul_apply,
        coloredAmbient_fderiv_coordinate color χ ℓ T x v hd c, coloredAmbient,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    ac_rfl
  simpa only [mul_assoc] using hv

end GlobalEmbedding.Initialization
