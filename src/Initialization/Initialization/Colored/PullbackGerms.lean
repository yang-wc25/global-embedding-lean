import Initialization.Colored.WaveErrorJets
import Initialization.Colored.NativeReferenceJets

/-!
# Actual chart pullbacks: local multiplicity without a false global support claim

A chart inverse is only continuous on its target. Consequently the topological
supports of its total-function pullbacks need not be disjoint outside that
target. The proofs here transfer the actual source germs through continuity at
the point, and never postulate global support separation for those pullbacks.
-/

noncomputable section
open Function Set Filter Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι X E : Type*} [Fintype ι] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pulling back an actual source germ needs continuity only at the point. -/
theorem coloredCoordinate_pullback_germ {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x) (c : Fin C) :
    (∃ i, color i = c ∧ φ x ∈ tsupport (χ i) ∧
      (coloredCoordinate color χ ℓ T c ∘ φ =ᶠ[𝓝 x]
        coloredWave (χ i ∘ φ) (ℓ i ∘ φ) T)) ∨
      (coloredCoordinate color χ ℓ T c ∘ φ =ᶠ[𝓝 x] 0) := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ φ x ∈ tsupport (χ i)
  · obtain ⟨i, hic, hxi⟩ := hactive
    left
    refine ⟨i, hic, hxi, ?_⟩
    subst c
    exact (coloredCoordinate_eventually_single color χ ℓ hdisjoint T (φ x) i hxi).comp_tendsto hφ
  · right
    exact (coloredCoordinate_eventually_zero color χ ℓ T c (φ x)
      (fun i hic hxi ↦ hactive ⟨i, hic, hxi⟩)).comp_tendsto hφ

/-- Every actual chart-coordinate jet is one active wave jet or zero, without
asserting global tsupport separation on the model vector space. -/
theorem coloredCoordinate_pullback_jet_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x)
    (c : Fin C) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ i, φ x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j (coloredWave (χ i ∘ φ) (ℓ i ∘ φ) T) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c ∘ φ) x‖ ≤ A := by
  rcases coloredCoordinate_pullback_germ color χ ℓ hdisjoint T φ x hφ c with
    ⟨i, _, hi, hg⟩ | hz
  · rw [(hg.iteratedFDeriv ℝ j).self_of_nhds]
    exact hterms i hi
  · rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero] using hA

/-- Smoothness of the pulled-back coordinate also only uses genuine source
supports. Arbitrary total-function values beyond chart targets cause no issue. -/
theorem coloredCoordinate_pullback_contDiffAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x) (c : Fin C)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i ∘ φ) x)
    (hℓ : ∀ i, φ x ∈ tsupport (χ i) → ContDiffAt ℝ ∞ (ℓ i ∘ φ) x) :
    ContDiffAt ℝ ∞ (coloredCoordinate color χ ℓ T c ∘ φ) x := by
  rcases coloredCoordinate_pullback_germ color χ ℓ hdisjoint T φ x hφ c with
    ⟨i, _, hi, hg⟩ | hz
  · exact ((hχ i).smul ((coloredExponential_contDiff T).contDiffAt.comp x
      (hℓ i hi))).congr_of_eventuallyEq hg
  · exact contDiffAt_const.congr_of_eventuallyEq hz

/-- The literal ambient pullback is smooth by its actual finitely many color
coordinates, with no extension assumed for the chart inverse. -/
theorem coloredAmbient_pullback_contDiffAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i ∘ φ) x)
    (hℓ : ∀ i, φ x ∈ tsupport (χ i) → ContDiffAt ℝ ∞ (ℓ i ∘ φ) x) :
    ContDiffAt ℝ ∞ (coloredAmbient color χ ℓ T ∘ φ) x := by
  have hp : ContDiffAt ℝ ∞ (fun y c ↦ coloredCoordinate color χ ℓ T c (φ y)) x :=
    contDiffAt_pi.mpr fun c ↦
      coloredCoordinate_pullback_contDiffAt color χ ℓ hdisjoint T φ x hφ c hχ hℓ
  exact PiLp.contDiff_toLp.contDiffAt.comp x hp

/-- The scalar first-derivative remainder for any actual coordinate function. -/
def coloredScalarFirstRemainder (w : E → ℂ) (r : E → E →L[ℝ] ℝ)
    (x : E) : E →L[ℝ] ℂ :=
  fderiv ℝ w x - (r x).smulRight ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) * w x)

@[simp] theorem coloredScalarFirstRemainder_wave (χ ℓ : E → ℝ) (T : ℝ)
    (r : E → E →L[ℝ] ℝ) :
    coloredScalarFirstRemainder (coloredWave χ ℓ T) r =
      coloredWaveFirstRemainder χ ℓ T r := rfl

@[simp] theorem coloredScalarFirstRemainder_zero (r : E → E →L[ℝ] ℝ) :
    coloredScalarFirstRemainder (0 : E → ℂ) r = 0 := by
  ext x v
  simp [coloredScalarFirstRemainder]

/-- A genuine equality on a neighborhood transfers the whole remainder field,
not merely its value or an independently assigned derivative. -/
theorem coloredScalarFirstRemainder_congr {w v : E → ℂ}
    (r : E → E →L[ℝ] ℝ) (x : E) (h : w =ᶠ[𝓝 x] v) :
    coloredScalarFirstRemainder w r =ᶠ[𝓝 x] coloredScalarFirstRemainder v r := by
  filter_upwards [h, h.fderiv (𝕜 := ℝ)] with y hy hdy
  simp only [coloredScalarFirstRemainder, hy, hdy]

/-- Every actual C^j color remainder inherits the single-wave smallness with
constant one, even after a chart inverse which is only locally continuous. -/
theorem coloredCoordinate_pullback_error_jet_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i k, i ≠ k → color i = color k →
      Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (T : ℝ) (φ : E → X) (x : E) (hφ : ContinuousAt φ x)
    (c : Fin C) (r : E → E →L[ℝ] ℝ) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ i, φ x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j (coloredWaveFirstRemainder (χ i ∘ φ) (ℓ i ∘ φ) T r) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j
      (coloredScalarFirstRemainder (coloredCoordinate color χ ℓ T c ∘ φ) r) x‖ ≤ A := by
  rcases coloredCoordinate_pullback_germ color χ ℓ hdisjoint T φ x hφ c with
    ⟨i, _, hi, hg⟩ | hz
  · rw [((coloredScalarFirstRemainder_congr r x hg).iteratedFDeriv ℝ j).self_of_nhds]
    exact hterms i hi
  · rw [((coloredScalarFirstRemainder_congr r x hz).iteratedFDeriv ℝ j).self_of_nhds,
      coloredScalarFirstRemainder_zero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact hA

end GlobalEmbedding.Initialization
