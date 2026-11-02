import Initialization.Colored.SelectorFirstJet
import Initialization.Phase.GramFrame
import GlobalEmbedding.Paper.InducedMetric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The true induced metric of the actual colored selector map

The ideal Gram identity is derived from the same selector's accepted partial
Gram identity. The error is then bounded using the actual first-jet remainder.
The statement refers to the original `Paper.inducedMetric`, including its
native tangent-space casts, not a replacement tensor definition.
-/

noncomputable section
open Function Set Metric Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The same ideal derivative is exactly the already proved Gram frame applied
to the vector of actual common covector coefficients. -/
theorem coloredIdealSelectorDerivative_eq_gramFrame {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (z : FreeHopfProduct (fun _ : Fin n ↦ C))
    (r : Fin n → E →L[ℝ] ℝ) (v : E) :
    coloredIdealSelectorDerivative S z r v =
      gramFrame (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z)
        (WithLp.toLp 2 (fun l ↦ r l v)) := by
  simp only [coloredIdealSelectorDerivative, sum_apply,
    ContinuousLinearMap.smulRight_apply, gramFrame_apply, PiLp.toLp_apply]

/-- The ideal derivative's metric is literally the common coframe square sum,
by the partial Gram identity of that very selector. -/
theorem coloredIdealSelectorDerivative_gram {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (z : FreeHopfProduct (fun _ : Fin n ↦ C))
    (hGram : Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (r : Fin n → E →L[ℝ] ℝ) (v w : E) :
    inner ℝ (coloredIdealSelectorDerivative S z r v)
      (coloredIdealSelectorDerivative S z r w) = ∑ l, r l v * r l w := by
  rw [coloredIdealSelectorDerivative_eq_gramFrame,
    coloredIdealSelectorDerivative_eq_gramFrame, gramFrame_inner _ hGram]
  simp [PiLp.inner_apply, mul_comm]

/-- The norm of the ideal derivative is the actual Euclidean coframe norm. -/
theorem coloredIdealSelectorDerivative_norm {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (z : FreeHopfProduct (fun _ : Fin n ↦ C))
    (hGram : Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (r : Fin n → E →L[ℝ] ℝ) (v : E) :
    ‖coloredIdealSelectorDerivative S z r v‖ =
      ‖(WithLp.toLp 2 (fun l ↦ r l v) : EuclideanSpace ℝ (Fin n))‖ := by
  rw [coloredIdealSelectorDerivative_eq_gramFrame, gramFrame_norm _ hGram]

/-- The selected-map first derivative is the proved ideal derivative plus the
same literal derivative-difference remainder used by all later estimates. -/
theorem coloredSelector_fderiv_eq_ideal_add_remainder {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (r : E → Fin n → E →L[ℝ] ℝ) (x : E) :
    fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x =
      coloredIdealSelectorDerivative S (coloredProduct color χ ℓ hdisjoint hsquare T x) (r x) +
      coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x := by
  unfold coloredSelectorFirstRemainder
  abel

/-- The true scalar metric error follows from the actual first-jet remainder,
with explicit quadratic dependence. Nothing about the desired metric is assumed. -/
theorem coloredSelector_metric_error_of_first_remainder {n C : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hGram : ∀ z, Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (r : E → Fin n → E →L[ℝ] ℝ) (x v w : E)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hcoeff : ∀ u, ‖(WithLp.toLp 2 (fun l ↦ r x l u) : EuclideanSpace ℝ (Fin n))‖ ≤ L * ‖u‖)
    (hR : ‖coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x‖ ≤ ε) :
    |inner ℝ (fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x v)
      (fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x w) -
      ∑ l, r x l v * r x l w| ≤ (2 * L * ε + ε ^ 2) * ‖v‖ * ‖w‖ := by
  let z := coloredProduct color χ ℓ hdisjoint hsquare T x
  let J := coloredIdealSelectorDerivative S z (r x)
  let R := coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x
  have hJ (u : E) : ‖J u‖ ≤ L * ‖u‖ := by
    rw [coloredIdealSelectorDerivative_norm S z (hGram z)]
    exact hcoeff u
  have hRu (u : E) : ‖R u‖ ≤ ε * ‖u‖ :=
    (R.le_opNorm u).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg u))
  have hjet := coloredSelector_fderiv_eq_ideal_add_remainder S color χ ℓ hdisjoint hsquare T r x
  have hid : inner ℝ (fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x v)
      (fderiv ℝ (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x w) -
      ∑ l, r x l v * r x l w =
      inner ℝ (J v) (R w) + inner ℝ (R v) (J w) + inner ℝ (R v) (R w) := by
    rw [hjet]
    change inner ℝ (J v + R v) (J w + R w) - _ = _
    rw [inner_add_left, inner_add_right, inner_add_right,
      coloredIdealSelectorDerivative_gram S z (hGram z)]
    ring
  rw [hid, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖inner ℝ (J v) (R w)‖ + ‖inner ℝ (R v) (J w)‖ + ‖inner ℝ (R v) (R w)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖J v‖ * ‖R w‖ + ‖R v‖ * ‖J w‖ + ‖R v‖ * ‖R w‖ := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ ≤ (L * ‖v‖) * (ε * ‖w‖) + (ε * ‖v‖) * (L * ‖w‖) +
        (ε * ‖v‖) * (ε * ‖w‖) := by gcongr <;> first | exact hJ _ | exact hRu _
    _ = _ := by ring

/-- The original native inducedMetric on the actual coordinate map has the same
bound. Tangent vectors are transported using Mathlib's actual model cast. -/
theorem coloredSelector_inducedMetric_error_of_first_remainder {n C N : ℕ}
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → EuclideanSpace ℝ (Fin N))
    (hGram : ∀ z, Matrix.gram ℝ (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ C) l S z) = 1)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (r : E → Fin n → E →L[ℝ] ℝ) (x v w : E)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hcoeff : ∀ u, ‖(WithLp.toLp 2 (fun l ↦ r x l u) : EuclideanSpace ℝ (Fin n))‖ ≤ L * ‖u‖)
    (hR : ‖coloredSelectorFirstRemainder S color χ ℓ hdisjoint hsquare T r x‖ ≤ ε) :
    |inducedMetric (I := 𝓘(ℝ, E)) (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x
      ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w) -
      ∑ l, r x l v * r x l w| ≤ (2 * L * ε + ε ^ 2) * ‖v‖ * ‖w‖ := by
  rw [inducedMetric_apply, mfderiv_eq_fderiv]
  exact coloredSelector_metric_error_of_first_remainder S hGram color χ ℓ hdisjoint hsquare
    T r x v w L ε hL hε hcoeff hR

end GlobalEmbedding.Initialization
