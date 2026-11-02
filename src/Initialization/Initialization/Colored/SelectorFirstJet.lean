import Initialization.Colored.NativeFirstJet
import Initialization.Assembly.SelectorHopfDerivative

/-!
# The actual selected colored map and its first-jet remainder

The remainder is defined from the actual derivative of H=S(z), then identified
with the derivative of the fixed radial extension applied to the actual ambient
colored error. Thus the chain-rule comparison is a proved identity for the
same global map, not a separately prescribed formal jet.
-/

noncomputable section
open Function Set Metric Filter
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The native ambient product of the actual sphere-valued color factors. -/
def coloredProductAmbient {n C : ℕ} (color : ι → Fin C) (χ : ι → E → ℝ)
    (ℓ : Fin n → ι → E → ℝ) (T : ℝ) (x : E) :
    HopfProductAmbient (fun _ : Fin n ↦ C) := fun l ↦ coloredAmbient color χ (ℓ l) T x

/-- The literal common-rate derivative in all native sphere factors. -/
def coloredIdealProductDerivative {n C : ℕ}
    (z : HopfProductAmbient (fun _ : Fin n ↦ C)) (r : Fin n → E →L[ℝ] ℝ) :
    E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C) :=
  ContinuousLinearMap.pi (fun l ↦ coloredIdealAmbientDerivative (z l) (r l))

/-- The actual ambient first-jet error, as a field of continuous linear maps. -/
def coloredProductDerivativeError {n C : ℕ} (color : ι → Fin C) (χ : ι → E → ℝ)
    (ℓ : Fin n → ι → E → ℝ) (T : ℝ) (r : E → Fin n → E →L[ℝ] ℝ)
    (x : E) : E →L[ℝ] HopfProductAmbient (fun _ : Fin n ↦ C) :=
  fderiv ℝ (coloredProductAmbient color χ ℓ T) x -
    coloredIdealProductDerivative (coloredProductAmbient color χ ℓ T x) (r x)

@[simp] theorem coloredProductAmbient_eq_inclusion {n C : ℕ}
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) (x : E) :
    coloredProductAmbient color χ ℓ T x =
      hopfProductInclusion (fun _ : Fin n ↦ C)
        (coloredProduct color χ ℓ hdisjoint hsquare T x) := rfl

/-- The actual common-rate derivative is the sum of the native ambient Hopf
velocities at exactly the same sphere argument. -/
theorem coloredIdealProductDerivative_velocity {n C : ℕ}
    (z : FreeHopfProduct (fun _ : Fin n ↦ C)) (r : Fin n → E →L[ℝ] ℝ) (v : E) :
    coloredIdealProductDerivative (hopfProductInclusion (fun _ : Fin n ↦ C) z) r v =
      ∑ l, r l v • ambientHopfGenerator (fun _ : Fin n ↦ C) l z := by
  classical
  funext l
  simp [coloredIdealProductDerivative, coloredIdealAmbientDerivative,
    hopfProductInclusion, ambientHopfGenerator, Finset.sum_apply, smul_ite]

/-- The product ambient derivative is the Pi of the actual factor derivatives. -/
theorem coloredProductAmbient_hasFDerivAt {n C : ℕ}
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (x : E) (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ l i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ l i) x) :
    HasFDerivAt (coloredProductAmbient color χ ℓ T)
      (ContinuousLinearMap.pi (fun l ↦ fderiv ℝ (coloredAmbient color χ (ℓ l) T) x)) x := by
  apply hasFDerivAt_pi.mpr
  intro l
  exact (coloredAmbient_differentiableAt color χ (ℓ l) hdisjoint T x hχ (hℓ l)).hasFDerivAt

/-- A fixed palette bound controls the actual entire product first-jet error.
The native product model uses the finite Pi norm, so no source-dimension factor
or number-of-patches factor is introduced. -/
theorem coloredProductDerivativeError_bound {n C : ℕ}
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (T A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (x : E)
    (r : E → Fin n → E →L[ℝ] ℝ)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ l i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ l i) x)
    (hcutoff : ∀ i, x ∈ tsupport (χ i) → ‖fderiv ℝ (χ i) x‖ ≤ A)
    (hrate : ∀ l i, x ∈ tsupport (χ i) →
      ‖T • fderiv ℝ (ℓ l i) x - r x l‖ ≤ D) :
    ‖coloredProductDerivativeError color χ ℓ T r x‖ ≤
      ((C : ℝ) + 1) * (A + 2 * Real.pi * D) := by
  have hd := (coloredProductAmbient_hasFDerivAt color χ ℓ hdisjoint T x hχ hℓ).fderiv
  have heq : coloredProductDerivativeError color χ ℓ T r x =
      ContinuousLinearMap.pi (fun l ↦
        fderiv ℝ (coloredAmbient color χ (ℓ l) T) x -
        coloredIdealAmbientDerivative (coloredAmbient color χ (ℓ l) T x) (r x l)) := by
    simp only [coloredProductDerivativeError, hd, coloredIdealProductDerivative]
    rfl
  rw [heq]
  exact ContinuousLinearMap.norm_pi_le_of_le
    (fun l ↦ coloredAmbient_first_error_bound color χ (ℓ l) hdisjoint hsquare
      T A D hA hD x (r x l) hχ (hℓ l) hcutoff (hrate l)) (by positivity)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ideal derivative in the target is the literal sum of selector Hopf
velocities multiplied by the common rescaled coframe covectors. -/
def coloredIdealSelectorDerivative {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (z : FreeHopfProduct (fun _ : Fin n ↦ C)) (r : Fin n → E →L[ℝ] ℝ) : E →L[ℝ] F :=
  ∑ l, (r l).smulRight (freeHopfDeriv (fun _ : Fin n ↦ C) l S z)

/-- The remainder is an actual derivative difference of the very map (7.2). -/
def coloredSelectorFirstRemainder {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] F :=
  fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x -
    coloredIdealSelectorDerivative S (coloredProduct color χ ℓ hdisjoint hsquare T x) (r x)

/-- The one globally constructed selected map equals the actual ambient
extension composed with its literal ambient colored argument. -/
theorem coloredSelectorMap_eq_extension {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) :
    coloredSelectorMap S color χ ℓ hdisjoint hsquare T =
      selectorAmbientExtension (fun _ : Fin n ↦ C) S ∘ coloredProductAmbient color χ ℓ T := by
  funext x
  exact (selectorAmbientExtension_inclusion (fun _ : Fin n ↦ C) S
    (coloredProduct color χ ℓ hdisjoint hsquare T x)).symm

/-- The ideal ambient derivative maps to precisely the ideal selector derivative.
This is a theorem about actual Hopf orbits and the genuine native selector. -/
theorem coloredIdealSelectorDerivative_eq_comp {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (z : FreeHopfProduct (fun _ : Fin n ↦ C)) (r : Fin n → E →L[ℝ] ℝ) :
    coloredIdealSelectorDerivative S z r =
      (fderiv ℝ (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
        (hopfProductInclusion (fun _ : Fin n ↦ C) z)).comp
          (coloredIdealProductDerivative (hopfProductInclusion (fun _ : Fin n ↦ C) z) r) := by
  ext v
  simp only [coloredIdealSelectorDerivative, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rw [coloredIdealProductDerivative_velocity,
    selectorAmbientExtension_ideal_velocity (fun _ : Fin n ↦ C) S hS]

/-- The actual first-jet remainder equals the ambient derivative applied to the
actual colored phase error. This exact identity is the second-jet bridge input. -/
theorem coloredSelectorFirstRemainder_eq_comp {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ l i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ l i) x) :
    coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x =
      (fderiv ℝ (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
        (coloredProductAmbient color χ ℓ T x)).comp
          (coloredProductDerivativeError color χ ℓ T r x) := by
  have hd := (coloredProductAmbient_hasFDerivAt color χ ℓ hdisjoint T x hχ hℓ).differentiableAt
  have he := (selectorAmbientExtension_contDiffAt (fun _ : Fin n ↦ C) S hS
    (hopfProductInclusion_mem_radial (fun _ : Fin n ↦ C)
      (coloredProduct color χ ℓ hdisjoint hsquare T x))).differentiableAt (by simp)
  have hchain : fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x =
      (fderiv ℝ (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
        (coloredProductAmbient color χ ℓ T x)).comp
          (fderiv ℝ (coloredProductAmbient color χ ℓ T) x) := by
    rw [coloredSelectorMap_eq_extension]
    exact fderiv_comp x he hd
  rw [coloredSelectorFirstRemainder, hchain,
    coloredIdealSelectorDerivative_eq_comp S hS]
  change _ = _
  rw [coloredProductDerivativeError, ContinuousLinearMap.comp_sub]
  rfl

/-- The selected map's actual first-jet error inherits the palette-only bound
from the genuine ambient argument. The extension bound B is fixed from the one
compact selector before choosing K,T. -/
theorem coloredSelectorFirstRemainder_bound {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (T A D B : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (x : E)
    (r : E → Fin n → E →L[ℝ] ℝ)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hℓ : ∀ l i, x ∈ tsupport (χ i) → DifferentiableAt ℝ (ℓ l i) x)
    (hcutoff : ∀ i, x ∈ tsupport (χ i) → ‖fderiv ℝ (χ i) x‖ ≤ A)
    (hrate : ∀ l i, x ∈ tsupport (χ i) →
      ‖T • fderiv ℝ (ℓ l i) x - r x l‖ ≤ D)
    (hext : ‖fderiv ℝ (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
      (coloredProductAmbient color χ ℓ T x)‖ ≤ B) :
    ‖coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x‖ ≤
      B * (((C : ℝ) + 1) * (A + 2 * Real.pi * D)) := by
  rw [coloredSelectorFirstRemainder_eq_comp S hS color χ ℓ hdisjoint hsquare T r x hχ hℓ]
  calc
    _ ≤ ‖fderiv ℝ (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
        (coloredProductAmbient color χ ℓ T x)‖ *
        ‖coloredProductDerivativeError color χ ℓ T r x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * (((C : ℝ) + 1) * (A + 2 * Real.pi * D)) :=
      mul_le_mul hext (coloredProductDerivativeError_bound color χ ℓ hdisjoint hsquare
        T A D hA hD x r hχ hℓ hcutoff hrate) (norm_nonneg _) hB

end GlobalEmbedding.Initialization
