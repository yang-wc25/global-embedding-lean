import Initialization.Colored.SourceReferenceJets
import Initialization.Colored.NativeErrorJets
import GlobalEmbedding.Paper.OperatorCompositionCjBound

/-!
# Actual selected-map C^j remainders

The actual first error of H=S(z) is the fixed outer derivative applied to the
actual ambient error. The existing, compiled bilinear composition estimate is
used directly, retaining the small parameter in all orders and in the actual
finite derivative-supremum norm.
-/

noncomputable section
open Function Set Filter Metric
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The native sphere-source error is exactly the already estimated native Pi
error. This connects the arbitrary chart pullback to the same actual second-jet
bridge and introduces no additional frame or formal derivative. -/
theorem selectorSourceAmbientError_eq_native {n C : ℕ}
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) :
    selectorSourceAmbientError (fun _ : Fin n ↦ C) z r =
      nativeProductFirstRemainder (selectorSourceAmbient (fun _ : Fin n ↦ C) z) r := by
  funext x
  unfold selectorSourceAmbientError nativeProductFirstRemainder
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  change selectorSourceIdealAmbient (fun _ : Fin n ↦ C) z r x v =
    coloredIdealProductDerivative (hopfProductInclusion (fun _ : Fin n ↦ C) (z x)) (r x) v
  rw [coloredIdealProductDerivative_velocity]
  simp only [selectorSourceIdealAmbient, sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The actual ambient error is smooth on every genuine coordinate domain. -/
theorem selectorSourceAmbientError_contDiffOn {n C : ℕ}
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient (fun _ : Fin n ↦ C) z) O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O) :
    ContDiffOn ℝ ∞ (selectorSourceAmbientError (fun _ : Fin n ↦ C) z r) O := by
  rw [selectorSourceAmbientError_eq_native]
  exact nativeProductFirstRemainder_contDiffOn _ r O hO hZ hr

/-- The same selected map's actual first error has genuine C^j smallness. The
outer-jet constant is fixed from the compact selector and the reference jets;
the ambient error constant is fixed by the actual colored phase estimates. -/
theorem selectorSourceFirstError_cj_bound {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (z : E → FreeHopfProduct (fun _ : Fin n ↦ C))
    (r : E → Fin n → E →L[ℝ] ℝ) (j : ℕ) (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (selectorSourceAmbient (fun _ : Fin n ↦ C) z) O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O)
    (a b δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (houter : ∀ k ≤ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ k (selectorSourceOuterDerivative (fun _ : Fin n ↦ C) S z) x‖ ≤ a)
    (herror : ∀ k ≤ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ k (selectorSourceAmbientError (fun _ : Fin n ↦ C) z r) x‖ ≤ b * δ) :
    (∀ k ≤ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ k (selectorSourceFirstError (fun _ : Fin n ↦ C) S z r) x‖ ≤
        ((2 : ℝ) ^ k * a * b) * δ) ∧
    finiteCjNorm j (selectorSourceFirstError (fun _ : Fin n ↦ C) S z r) O ≤
      ((∑ k ∈ Finset.range (j+1), (2 : ℝ) ^ k) * a * b) * δ := by
  have heq : EqOn (selectorSourceFirstError (fun _ : Fin n ↦ C) S z r)
      (fun x ↦ (selectorSourceOuterDerivative (fun _ : Fin n ↦ C) S z x).comp
        (selectorSourceAmbientError (fun _ : Fin n ↦ C) z r x)) O := by
    intro x hx
    exact selectorSourceFirstError_eq_comp (fun _ : Fin n ↦ C) S hS z r
      ((hZ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
  have h := operator_composition_cj_bound j O hO
    (selectorSourceOuterDerivative (fun _ : Fin n ↦ C) S z)
    (selectorSourceAmbientError (fun _ : Fin n ↦ C) z r)
    (selectorSourceFirstError (fun _ : Fin n ↦ C) S z r)
    (selectorSourceOuterDerivative_contDiffOn (fun _ : Fin n ↦ C) S hS z O hO hZ)
    (selectorSourceAmbientError_contDiffOn z r O hO hZ hr)
    a (b*δ) ha (mul_nonneg hb hδ) houter herror heq
  constructor
  · intro k hk x hx
    simpa only [mul_assoc] using h.1 k hk x hx
  · simpa only [mul_assoc] using h.2.2

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- The scalar wave remainders of an actual source family supply the genuine
sphere-source ambient error after an actual local coordinate pullback. -/
theorem coloredSourceAmbientError_jet_bound {n C : ℕ}
    (color : ι → Fin C) (χ : ι → X → ℝ) (ℓ : Fin n → ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (T : ℝ) (φ : E → X) (r : E → Fin n → E →L[ℝ] ℝ)
    (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (fun y l ↦ coloredAmbient color χ (ℓ l) T (φ y)) O)
    (hr : ∀ l, ContDiffOn ℝ ∞ (fun y ↦ r y l) O)
    (x : E) (hx : x ∈ O) (hφ : ContinuousAt φ x) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ l i, φ x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j
        (coloredWaveFirstRemainder (χ i ∘ φ) (ℓ l i ∘ φ) T (fun y ↦ r y l)) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j
      (selectorSourceAmbientError (fun _ : Fin n ↦ C)
        (coloredProduct color χ ℓ hdisjoint hsquare T ∘ φ) r) x‖ ≤ ((C : ℝ) + 1) * A := by
  rw [selectorSourceAmbientError_eq_native]
  exact coloredProduct_pullback_error_jet_bound color χ ℓ hdisjoint T φ r O hO hZ hr
    x hx hφ j A hA hterms

end GlobalEmbedding.Initialization
