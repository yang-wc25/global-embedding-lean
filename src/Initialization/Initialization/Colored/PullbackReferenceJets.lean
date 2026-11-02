import Initialization.Colored.PullbackGerms

/-! # Native whole-product reference jets from actual source germs -/

noncomputable section
open Function Set Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι X E : Type*} [Fintype ι] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar actual wave bounds yield the whole-product reference bound after
any locally continuous source pullback. The actual ambient map is the one
whose smooth germ is used; pullback support separation is never assumed. -/
theorem coloredProduct_pullback_reference_jet_bound {n C : ℕ}
    (color : ι → Fin C) (χ : ι → X → ℝ) (ℓ : Fin n → ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x)
    (hZ : ContDiffAt ℝ ∞ (fun y l ↦ coloredAmbient color χ (ℓ l) T (φ y)) x)
    (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ l i, φ x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j (coloredWave (χ i ∘ φ) (ℓ l i ∘ φ) T) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (fun y l ↦ coloredAmbient color χ (ℓ l) T (φ y)) x‖ ≤
      ((C : ℝ) + 1) * A := by
  apply coloredProductAmbient_jet_bound color (fun i ↦ χ i ∘ φ)
    (fun l i ↦ ℓ l i ∘ φ) T x hZ j (((C : ℝ) + 1) * A) (by positivity)
  intro l
  apply coloredAmbient_jet_bound color (fun i ↦ χ i ∘ φ) (fun i ↦ ℓ l i ∘ φ) T x
    (contDiffAt_pi.mp hZ l) j A hA
  intro c
  exact coloredCoordinate_pullback_jet_bound color χ (ℓ l) hdisjoint T φ x hφ c j A hA
    (hterms l)

end GlobalEmbedding.Initialization
