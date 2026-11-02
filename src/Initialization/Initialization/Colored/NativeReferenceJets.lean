import Initialization.Colored.SelectorFirstJet
import Initialization.Colored.ReferenceJets

/-!
# Native vector and whole-product reference jets

The bounds use the fixed palette size, not the number of local patches. Every
jet is the iterated Fréchet derivative of the literal map already constructed.
-/

noncomputable section
open Function Set Metric Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise smoothness of a color coordinate requires phase smoothness only
on the actual active support. -/
theorem coloredCoordinate_contDiffAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (c : Fin C) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → ContDiffAt ℝ ∞ (ℓ i) x) :
    ContDiffAt ℝ ∞ (coloredCoordinate color χ ℓ T c) x := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ x ∈ tsupport (χ i)
  · obtain ⟨i, hic, hxi⟩ := hactive
    subst c
    have hw : ContDiffAt ℝ ∞ (coloredWave (χ i) (ℓ i) T) x :=
      (hχ i).smul ((coloredExponential_contDiff T).contDiffAt.comp x (hℓ i hxi))
    exact hw.congr_of_eventuallyEq
      (coloredCoordinate_eventually_single color χ ℓ hdisjoint T x i hxi)
  · have hx : ∀ i, color i = c → x ∉ tsupport (χ i) := by
      intro i hic hxi
      exact hactive ⟨i, hic, hxi⟩
    exact contDiffAt_const.congr_of_eventuallyEq
      (coloredCoordinate_eventually_zero color χ ℓ T c x hx)

/-- Actual ambient smoothness at a point follows through the native PiL² map. -/
theorem coloredAmbient_contDiffAt {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hℓ : ∀ i, x ∈ tsupport (χ i) → ContDiffAt ℝ ∞ (ℓ i) x) :
    ContDiffAt ℝ ∞ (coloredAmbient color χ ℓ T) x := by
  have hp : ContDiffAt ℝ ∞ (fun y c ↦ coloredCoordinate color χ ℓ T c y) x :=
    contDiffAt_pi.mpr (fun c ↦ coloredCoordinate_contDiffAt color χ ℓ hdisjoint T c x hχ hℓ)
  exact PiLp.contDiff_toLp.contDiffAt.comp x hp

/-- Every actual ambient jet has exactly the jets of its literal color
coordinates, by composition with the continuous real coordinate projection. -/
theorem coloredAmbient_jet_coordinate {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ) (T : ℝ) (x : E)
    (h : ContDiffAt ℝ ∞ (coloredAmbient color χ ℓ T) x)
    (j : ℕ) (v : Fin j → E) (c : Fin C) :
    (iteratedFDeriv ℝ j (coloredAmbient color χ ℓ T) x v) c =
      iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x v := by
  let p : PlanarHopfAmbient C →L[ℝ] ℂ := (EuclideanSpace.proj c).restrictScalars ℝ
  have heq : p ∘ coloredAmbient color χ ℓ T = coloredCoordinate color χ ℓ T c := rfl
  have hp := p.iteratedFDeriv_comp_left h (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [heq] at hp
  exact (congrArg (fun L ↦ L v) hp).symm

/-- Fixed palette size controls the entire native complex Euclidean jet. -/
theorem coloredAmbient_jet_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ) (T : ℝ) (x : E)
    (h : ContDiffAt ℝ ∞ (coloredAmbient color χ ℓ T) x)
    (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hcoordinates : ∀ c, ‖iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (coloredAmbient color χ ℓ T) x‖ ≤ ((C : ℝ) + 1) * A := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hb : ‖iteratedFDeriv ℝ j (coloredAmbient color χ ℓ T) x v‖ ≤
      ((C : ℝ) + 1) * (A * ∏ i, ‖v i‖) := by
    apply complexEuclidean_norm_le_coordinate_bound _ _ (by positivity)
    intro c
    rw [coloredAmbient_jet_coordinate color χ ℓ T x h j v c]
    exact (iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x).le_of_opNorm_le
      (hcoordinates c) v
  simpa only [mul_assoc] using hb

/-- Scalar wave reference estimates supply the actual vector reference estimate.
Only active terms require a smooth phase neighborhood and phase-rate budget. -/
theorem coloredAmbient_reference_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T A L : ℝ) (hA : 0 ≤ A) (x : E) (j : ℕ)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hlocal : ∀ i, x ∈ tsupport (χ i) →
      ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ContDiffOn ℝ ∞ (χ i) O ∧ ContDiffOn ℝ ∞ (ℓ i) O)
    (hcutoff : ∀ i, x ∈ tsupport (χ i) → ∀ k ≤ j, ‖iteratedFDeriv ℝ k (χ i) x‖ ≤ A)
    (hphase : ∀ i, x ∈ tsupport (χ i) → ∀ k, 1 ≤ k → k ≤ j →
      |T| * ‖iteratedFDeriv ℝ k (ℓ i) x‖ ≤ L) :
    ‖iteratedFDeriv ℝ j (coloredAmbient color χ ℓ T) x‖ ≤
      ((C : ℝ) + 1) * coloredWaveReferenceBound A L j := by
  have hℓ (i : ι) (hi : x ∈ tsupport (χ i)) : ContDiffAt ℝ ∞ (ℓ i) x := by
    obtain ⟨O, hO, hx, _, hℓ⟩ := hlocal i hi
    exact hℓ.contDiffAt (hO.mem_nhds hx)
  apply coloredAmbient_jet_bound color χ ℓ T x
    (coloredAmbient_contDiffAt color χ ℓ hdisjoint T x hχ hℓ) j
    (coloredWaveReferenceBound A L j) (coloredWaveReferenceBound_nonneg A L hA j)
  intro c
  apply coloredCoordinate_jet_bound color χ ℓ hdisjoint T c x j _
    (coloredWaveReferenceBound_nonneg A L hA j)
  intro i hi
  obtain ⟨O, hO, hx, hχO, hℓO⟩ := hlocal i hi
  exact coloredWave_reference_bound O hO (χ i) (ℓ i) hχO hℓO T A L hA x hx j
    (hcutoff i hi) (hphase i hi)

/-- The actual whole-product ambient map is smooth at the point. -/
theorem coloredProductAmbient_contDiffAt {n C : ℕ}
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (x : E)
    (hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) x)
    (hℓ : ∀ l i, x ∈ tsupport (χ i) → ContDiffAt ℝ ∞ (ℓ l i) x) :
    ContDiffAt ℝ ∞ (coloredProductAmbient color χ ℓ T) x :=
  contDiffAt_pi.mpr
    (fun l ↦ coloredAmbient_contDiffAt color χ (ℓ l) hdisjoint T x hχ (hℓ l))

/-- The native Pi norm retains the same factorwise bound on every true product
jet; the number of patches and the value of the frequency remain absent. -/
theorem coloredProductAmbient_jet_bound {n C : ℕ}
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (T : ℝ) (x : E)
    (h : ContDiffAt ℝ ∞ (coloredProductAmbient color χ ℓ T) x)
    (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hfactors : ∀ l, ‖iteratedFDeriv ℝ j (coloredAmbient color χ (ℓ l) T) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (coloredProductAmbient color χ ℓ T) x‖ ≤ A := by
  apply ContinuousMultilinearMap.opNorm_le_bound hA
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro l
  let p : HopfProductAmbient (fun _ : Fin n ↦ C) →L[ℝ] PlanarHopfAmbient C :=
    ContinuousLinearMap.proj l
  have heq : p ∘ coloredProductAmbient color χ ℓ T = coloredAmbient color χ (ℓ l) T := rfl
  have hp := p.iteratedFDeriv_comp_left h (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [heq] at hp
  have hv := congrArg (fun L ↦ L v) hp
  change iteratedFDeriv ℝ j (coloredAmbient color χ (ℓ l) T) x v =
    p (iteratedFDeriv ℝ j (coloredProductAmbient color χ ℓ T) x v) at hv
  change ‖p (iteratedFDeriv ℝ j (coloredProductAmbient color χ ℓ T) x v)‖ ≤ _
  rw [← hv]
  exact (iteratedFDeriv ℝ j (coloredAmbient color χ (ℓ l) T) x).le_of_opNorm_le (hfactors l) v

end GlobalEmbedding.Initialization
