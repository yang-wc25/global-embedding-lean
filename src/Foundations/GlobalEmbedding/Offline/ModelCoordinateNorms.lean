import GlobalEmbedding.Offline.PaperSmoothingEstimates

/-!
# Actual coordinate norms under a continuous linear model equivalence

Source: `main.tex` 234 and 700–720, the original Euclidean chart models and
their component-coordinate norms. All derivatives here are native Fréchet
derivatives of the same functions. The two directions retain their actual
operator-norm factors; a Euclidean/sup-norm isometry is never asserted.
The cumulative factors are explicit and do not depend on an atlas or its size.
-/

open GlobalEmbedding.Paper Function Set
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

section LinearTransport

variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cumulative native derivative cost of a fixed linear change of source model. -/
def linearModelFactor (e : E ≃L[ℝ] G) (j : ℕ) : ℝ :=
  (max 1 ‖e.toContinuousLinearMap‖) ^ j

theorem linearModelFactor_nonneg (e : E ≃L[ℝ] G) (j : ℕ) :
    0 ≤ linearModelFactor e j := pow_nonneg (le_max_iff.mpr (Or.inl zero_le_one)) _

theorem linearModelFactor_mono (e : E ≃L[ℝ] G) {j k : ℕ} (hjk : j ≤ k) :
    linearModelFactor e j ≤ linearModelFactor e k := pow_le_pow_right₀ (le_max_left _ _) hjk

/-- Unconditional all-order native chain rule for an invertible linear source
change, followed by the actual multilinear operator-norm inequality. -/
theorem norm_iteratedFDeriv_comp_equiv_le (e : E ≃L[ℝ] G) (f : G → F) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f ∘ e) x‖ ≤
      ‖iteratedFDeriv ℝ j f (e x)‖ * linearModelFactor e j := by
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (norm_nonneg _)

end LinearTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d q : ℕ} {ι : Type*} [Fintype ι]

/-- The actual Pi-coordinate presentation of a function on the original model. -/
def modelCoordinateFamily (e : E ≃L[ℝ] (Fin d → ℝ)) (f : ι → E → Fin q → ℝ) :=
  fun i => f i ∘ e.symm

/-- The actual pullback of a differentiation or evaluation domain. -/
def modelCoordinateDomains (e : E ≃L[ℝ] (Fin d → ℝ)) (S : ι → Set E) :=
  fun i => e.symm ⁻¹' S i

/-- Native-to-coordinate comparison cost for all orders through j. -/
def nativeCoordinateFactor (e : E ≃L[ℝ] (Fin d → ℝ)) (j : ℕ) : ℝ :=
  linearModelFactor e j * coordinateDimensionFactor d j

theorem nativeCoordinateFactor_nonneg (e : E ≃L[ℝ] (Fin d → ℝ)) (j : ℕ) :
    0 ≤ nativeCoordinateFactor e j :=
  mul_nonneg (linearModelFactor_nonneg e j) (coordinateDimensionFactor_nonneg d j)

theorem nativeCoordinateFactor_mono (e : E ≃L[ℝ] (Fin d → ℝ)) {j k : ℕ} (hjk : j ≤ k) :
    nativeCoordinateFactor e j ≤ nativeCoordinateFactor e k :=
  mul_le_mul (linearModelFactor_mono e hjk) (coordinateDimensionFactor_mono d hjk)
    (coordinateDimensionFactor_nonneg d j) (linearModelFactor_nonneg e k)

omit [Fintype ι] in
theorem modelCoordinateDomains_open (e : E ≃L[ℝ] (Fin d → ℝ)) {O : ι → Set E}
    (hO : ∀ i, IsOpen (O i)) (i : ι) : IsOpen (modelCoordinateDomains e O i) :=
  (hO i).preimage e.symm.continuous

omit [Fintype ι] in
theorem modelCoordinateFamily_contDiffOn (e : E ≃L[ℝ] (Fin d → ℝ))
    {f : ι → E → Fin q → ℝ} {O : ι → Set E}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (i : ι) :
    ContDiffOn ℝ ∞ (modelCoordinateFamily e f i) (modelCoordinateDomains e O i) :=
  (hf i).comp e.symm.contDiff.contDiffOn (fun _ hx => hx)

/-- Finiteness of the original coordinate norm bounds genuine native jets on
the original model. The reverse chain rule includes the model's operator norm. -/
theorem paperAtlasCj_model_native_jet_le (e : E ≃L[ℝ] (Fin d → ℝ))
    (j : ℕ) (f : ι → E → Fin q → ℝ) (O S : ι → Set E)
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : paperAtlasCj j (modelCoordinateFamily e f)
      (modelCoordinateDomains e O) (modelCoordinateDomains e S) ≠ ⊤)
    (i : ι) {k : ℕ} (hk : k ≤ j) {x : E} (hx : x ∈ S i) :
    ‖iteratedFDeriv ℝ k (f i) x‖ ≤ nativeCoordinateFactor e j *
      (paperAtlasCj j (modelCoordinateFamily e f)
        (modelCoordinateDomains e O) (modelCoordinateDomains e S)).toReal := by
  have hcoord := paperAtlasCj_jet_le j (modelCoordinateFamily e f)
    (modelCoordinateDomains e O) (modelCoordinateDomains e S)
    (modelCoordinateDomains_open e hO) (fun i _ hx => hSO i hx)
    (modelCoordinateFamily_contDiffOn e hf) hfinite i hk
    (x := e x) (by simpa only [modelCoordinateDomains, mem_preimage, e.symm_apply_apply] using hx)
  have h := norm_iteratedFDeriv_comp_equiv_le e (modelCoordinateFamily e f i) k x
  have hfun : modelCoordinateFamily e f i ∘ e = f i := by funext y; simp [modelCoordinateFamily]
  rw [hfun] at h
  apply h.trans
  calc
    _ ≤ (coordinateDimensionFactor d j * (paperAtlasCj j (modelCoordinateFamily e f)
        (modelCoordinateDomains e O) (modelCoordinateDomains e S)).toReal) * linearModelFactor e j :=
      mul_le_mul hcoord (linearModelFactor_mono e hk) (linearModelFactor_nonneg e k)
        (mul_nonneg (coordinateDimensionFactor_nonneg d j) ENNReal.toReal_nonneg)
    _ = _ := by unfold nativeCoordinateFactor; ring

/-- Actual native jet bounds imply the original coordinate norm bound, with
the forward operator-norm factor and explicit finiteness before real projection. -/
theorem paperAtlasCj_model_le_of_native_bound (e : E ≃L[ℝ] (Fin d → ℝ))
    (j : ℕ) (f : ι → E → Fin q → ℝ) (O S : ι → Set E)
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i, ∀ k ≤ j, ∀ x ∈ S i, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ R) :
    paperAtlasCj j (modelCoordinateFamily e f) (modelCoordinateDomains e O)
      (modelCoordinateDomains e S) ≤ ENNReal.ofReal (linearModelFactor e.symm j * R) := by
  apply paperAtlasCj_le_of_jet_bound j (modelCoordinateFamily e f)
    (modelCoordinateDomains e O) (modelCoordinateDomains e S) (modelCoordinateDomains_open e hO)
    (fun i _ hx => hSO i hx) (modelCoordinateFamily_contDiffOn e hf)
  intro i k hk x hx
  apply (norm_iteratedFDeriv_comp_equiv_le e.symm (f i) k x).trans
  exact (mul_le_mul (hbound i k hk _ hx) (linearModelFactor_mono e.symm hk)
    (linearModelFactor_nonneg e.symm k) hR).trans_eq (mul_comm _ _)

end

end GlobalEmbedding.Offline
