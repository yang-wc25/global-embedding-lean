import Initialization.Colored.PullbackGerms
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# All-order error of the actual ambient product in chart pullbacks

Scalar germ estimates are lifted to the genuine Pi-of-Euclidean-space norm.
The only multiplicity factor is the palette chosen before K and T. No bound
depending on the number of net points is introduced.
-/

noncomputable section
open Function Set Filter Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hopfAmbientCoordinate {n C : ℕ} (l : Fin n) (c : Fin C) :
    HopfProductAmbient (fun _ : Fin n ↦ C) →L[ℝ] ℂ :=
  ((EuclideanSpace.proj c).restrictScalars ℝ).comp (ContinuousLinearMap.proj l)

def hopfCovectorCoordinate {n C : ℕ} (l : Fin n) (c : Fin C) :
    (E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C)) →L[ℝ] (E →L[ℝ] ℂ) :=
  ContinuousLinearMap.compL ℝ E _ _ (hopfAmbientCoordinate l c)

@[simp] theorem hopfCovectorCoordinate_apply {n C : ℕ} (l : Fin n) (c : Fin C)
    (L : E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C)) (v : E) :
    hopfCovectorCoordinate l c L v = (L v l) c := rfl

/-- This is a bound on the actual iterated derivative of an operator field,
with the fixed palette factor and the native finite Pi norm. -/
theorem nativeProductCovector_jet_bound {n C : ℕ}
    (R : E → E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C)) (x : E)
    (hR : ContDiffAt ℝ ∞ R x) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hcoordinates : ∀ l c,
      ‖iteratedFDeriv ℝ j (hopfCovectorCoordinate l c ∘ R) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j R x‖ ≤ ((C : ℝ) + 1) * A := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro l
  have hb : ‖iteratedFDeriv ℝ j R x v u l‖ ≤
      ((C : ℝ) + 1) * ((A * ∏ i, ‖v i‖) * ‖u‖) := by
    apply complexEuclidean_norm_le_coordinate_bound _ _ (by positivity)
    intro c
    have hp := (hopfCovectorCoordinate (E := E) l c).iteratedFDeriv_comp_left hR
      (by simp : (j : ℕ∞ω) ≤ ∞)
    have hv := congrArg (fun L ↦ L v u) hp
    change iteratedFDeriv ℝ j (hopfCovectorCoordinate l c ∘ R) x v u =
      (iteratedFDeriv ℝ j R x v u l) c at hv
    rw [← hv]
    exact ((iteratedFDeriv ℝ j (hopfCovectorCoordinate l c ∘ R) x v).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right
        ((iteratedFDeriv ℝ j (hopfCovectorCoordinate l c ∘ R) x).le_of_opNorm_le
          (hcoordinates l c) v) (norm_nonneg u))
  simpa only [mul_assoc] using hb

/-- The common-rate error of any actual native ambient product map. -/
def nativeProductFirstRemainder {n C : ℕ}
    (Z : E → HopfProductAmbient (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) :
    E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C) :=
  fderiv ℝ Z x - coloredIdealProductDerivative (Z x) (r x)

/-- Each projected actual operator remainder is exactly the scalar coordinate
remainder. The proof uses the actual chain rule for the coordinate projection. -/
theorem nativeProductFirstRemainder_coordinate {n C : ℕ}
    (Z : E → HopfProductAmbient (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) (hZ : DifferentiableAt ℝ Z x)
    (l : Fin n) (c : Fin C) :
    hopfCovectorCoordinate l c (nativeProductFirstRemainder Z r x) =
      coloredScalarFirstRemainder (fun y ↦ (Z y l) c) (fun y ↦ r y l) x := by
  let p := hopfAmbientCoordinate l c
  have hd := (p.hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  ext v
  change (p (fderiv ℝ Z x v) - p (coloredIdealProductDerivative (Z x) (r x) v)) = _
  have hdv := congrArg (fun L : E →L[ℝ] ℂ ↦ L v) hd
  change fderiv ℝ (p ∘ Z) x v = p (fderiv ℝ Z x v) at hdv
  rw [← hdv]
  change fderiv ℝ (fun y ↦ (Z y l) c) x v - _ = _
  simp only [coloredScalarFirstRemainder, sub_apply, ContinuousLinearMap.smulRight_apply]
  congr 1

variable [FiniteDimensional ℝ E]

theorem nativeProductFirstRemainder_contDiffOn {n C : ℕ}
    (Z : E → HopfProductAmbient (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ Z O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O) :
    ContDiffOn ℝ ∞ (nativeProductFirstRemainder Z r) O := by
  apply (hZ.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).sub
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro l
  exact ((hr l).clm_apply contDiffOn_const).smul
    ((contDiffOn_pi.mp hZ l).const_smul ((((2 * Real.pi : ℝ) : ℂ) * Complex.I)))

/-- The product first error has the all-order bound whenever its actual scalar
remainders do. Local smoothness is used only on the given open coordinate domain. -/
theorem nativeProductFirstRemainder_jet_bound {n C : ℕ}
    (Z : E → HopfProductAmbient (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ Z O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O)
    (x : E) (hx : x ∈ O) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hscalar : ∀ l c, ‖iteratedFDeriv ℝ j
      (coloredScalarFirstRemainder (fun y ↦ (Z y l) c) (fun y ↦ r y l)) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (nativeProductFirstRemainder Z r) x‖ ≤ ((C : ℝ) + 1) * A := by
  apply nativeProductCovector_jet_bound _ x
    ((nativeProductFirstRemainder_contDiffOn Z r O hO hZ hr).contDiffAt (hO.mem_nhds hx))
    j A hA
  intro l c
  have he : hopfCovectorCoordinate l c ∘ nativeProductFirstRemainder Z r =ᶠ[𝓝 x]
      coloredScalarFirstRemainder (fun y ↦ (Z y l) c) (fun y ↦ r y l) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact nativeProductFirstRemainder_coordinate Z r y
      ((hZ.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) l c
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  exact hscalar l c

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- The local scalar estimate is consumed directly from genuine source
supports. This is the all-order ambient error for the actual chart pullback. -/
theorem coloredProduct_pullback_error_jet_bound {n C : ℕ}
    (color : ι → Fin C) (χ : ι → X → ℝ) (ℓ : Fin n → ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (r : E → Fin n → E →L[ℝ] ℝ)
    (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (fun y l ↦ coloredAmbient color χ (ℓ l) T (φ y)) O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O)
    (x : E) (hx : x ∈ O) (hφ : ContinuousAt φ x) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ l i, φ x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j
        (coloredWaveFirstRemainder (χ i ∘ φ) (ℓ l i ∘ φ) T (fun y ↦ r y l)) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j
      (nativeProductFirstRemainder (fun y l ↦ coloredAmbient color χ (ℓ l) T (φ y)) r) x‖ ≤
        ((C : ℝ) + 1) * A := by
  apply nativeProductFirstRemainder_jet_bound _ r O hO hZ hr x hx j A hA
  intro l c
  exact coloredCoordinate_pullback_error_jet_bound color χ (ℓ l) hdisjoint T φ x hφ c
    (fun y ↦ r y l) j A hA (hterms l)

end GlobalEmbedding.Initialization
