import GlobalEmbedding.Offline.LocalSmoothingDerivatives
import GlobalEmbedding.Offline.IteratedJetNorms

/-!
# Actual derivative gain using only a bounded local sampling buffer

Source: `main.tex` 700–719, derivative gain in the buffered smoothing lemma.
The source is unrestricted away from the actual sampling buffer. For the
proof only, its bounded zero extension from that buffer is locally integrable.
The same convolution agrees with the original one on the original open
output set, hence has exactly the same native jets there. Kernel derivatives
therefore give genuine local gain without a global source integrability or
compact-support assumption. The operator itself is not replaced.
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

omit [NormedSpace ℝ F] in
/-- The true zero extension of a function bounded and continuous on an open
buffer is locally integrable everywhere, including its actual boundary. -/
theorem bounded_buffer_indicator_locallyIntegrable {u : E → F} {V : Set E}
    (hV : IsOpen V) (hu : ContinuousOn u V) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ V, ‖u y‖ ≤ B) : LocallyIntegrable (V.indicator u) mu := by
  have hmeas : AEStronglyMeasurable (V.indicator u) mu :=
    (aestronglyMeasurable_indicator_iff hV.measurableSet).mpr
      (hu.aestronglyMeasurable hV.measurableSet)
  apply (locallyIntegrable_const (μ := mu) B).mono hmeas
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg hB]
  by_cases hy : y ∈ V
  · rw [indicator_of_mem hy]
    exact hbound y hy
  · simp only [indicator_of_notMem hy, norm_zero]
    exact hB

omit [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Restricting the source to a genuine sampling buffer leaves the ACTUAL
integral unchanged at every point whose kernel samples stay in that buffer. -/
theorem signedSmoothing_buffer_indicator_eq {u : E → F} {K : E → ℝ}
    {V : Set E} (ell : ℝ) (x : E)
    (hbuffer : ∀ y ∈ tsupport K, x - ell • y ∈ V) :
    signedSmoothing mu K ell (V.indicator u) x = signedSmoothing mu K ell u x := by
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ tsupport K
  · rw [indicator_of_mem (hbuffer y hy)]
  · simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- Genuine native derivative gain on an open output domain, from a C0 bound
on its actual sampling buffer. No assumption concerns the source outside V. -/
theorem signedSmoothing_local_derivative_gain {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hu : ContinuousOn u V)
    {ell : ℝ} (hell : 0 < ell)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y ∈ V, ‖u y‖ ≤ B)
    (j : ℕ) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (signedSmoothing mu K ell u) x‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have hg := bounded_buffer_indicator_locallyIntegrable mu hV hu B hB hbound
  have heq : signedSmoothing mu K ell (V.indicator u) =ᶠ[𝓝 x] signedSmoothing mu K ell u := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact signedSmoothing_buffer_indicator_eq mu ell z (hbuffer z hz)
  rw [← (heq.iteratedFDeriv ℝ j).eq_of_nhds]
  apply signedSmoothing_iteratedFDeriv_norm_le mu hK hcompact hg hell j x B
  intro y _
  by_cases hy : x - y ∈ V
  · rw [indicator_of_mem hy]
    exact hbound _ hy
  · simp only [indicator_of_notMem hy, norm_zero]
    exact hB

variable [CompleteSpace F]

/-- First keep the actual base jet on the source, then move the additional
derivatives onto the actual kernel. The local source-jet identity and its
neighborhood equality identify this with the SAME total derivative of S u. -/
theorem signedSmoothing_local_shifted_gain {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V)
    (base j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ V, ‖iteratedFDeriv ℝ base u y‖ ≤ B)
    {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ (j + base) (signedSmoothing mu K ell u) x‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have hjet : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ base u) V := by
    intro y hy
    exact ((hu.contDiffAt (hV.mem_nhds hy)).iteratedFDeriv_right (by simp)).contDiffWithinAt
  have hcomm : iteratedFDeriv ℝ base (signedSmoothing mu K ell u) =ᶠ[𝓝 x]
      signedSmoothing mu K ell (iteratedFDeriv ℝ base u) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact signedSmoothing_iteratedFDeriv_source_on mu hK hcompact hU hV hu ell hbuffer base hy
  have h := signedSmoothing_local_derivative_gain mu hK hcompact hU hV hjet.continuousOn
    hell hbuffer B hB hbound j hx
  rw [← (hcomm.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_iteratedFDeriv] at h
  exact h

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Explicit cumulative fixed-kernel derivative L1 cost through order j. -/
def kernelGainConstant (K : E → ℝ) (j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (j + 1), ∫ y, ‖iteratedFDeriv ℝ a K y‖ ∂mu

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
theorem kernelGainConstant_nonneg (K : E → ℝ) (j : ℕ) : 0 ≤ kernelGainConstant mu K j :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
theorem kernelDerivative_L1_le_gainConstant (K : E → ℝ) {a j : ℕ} (haj : a ≤ j) :
    (∫ y, ‖iteratedFDeriv ℝ a K y‖ ∂mu) ≤ kernelGainConstant mu K j := by
  unfold kernelGainConstant
  exact Finset.single_le_sum (f := fun a : ℕ => ∫ y, ‖iteratedFDeriv ℝ a K y‖ ∂mu)
    (fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le haj))

/-- Every jet through j+base of the SAME local smoother costs at most ell^-j
times the original source C^base bound. This is a cumulative Cj estimate;
lower derivatives are included, and ell≤1 is used exactly in the power bound. -/
theorem signedSmoothing_local_cumulative_gain {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V)
    (base j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ b ≤ base, ∀ y ∈ V, ‖iteratedFDeriv ℝ b u y‖ ≤ B)
    {k : ℕ} (hk : k ≤ j + base) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k (signedSmoothing mu K ell u) x‖ ≤
      kernelGainConstant mu K j * B * (ell⁻¹)^j := by
  let b := min k base
  let a := k - b
  have hbk : b ≤ k := min_le_left _ _
  have hbb : b ≤ base := min_le_right _ _
  have hab : a + b = k := Nat.sub_add_cancel hbk
  have haj : a ≤ j := by dsimp [a, b]; omega
  have h := signedSmoothing_local_shifted_gain mu hK hcompact hU hV hu hell hbuffer
    b a B hB (hbound b hbb) hx
  rw [hab] at h
  apply h.trans
  have hinv : 1 ≤ ell⁻¹ := (one_le_inv₀ hell).mpr hell1
  calc
    _ ≤ (B * (ell⁻¹)^j) * kernelGainConstant mu K j :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv haj) hB)
        (kernelDerivative_L1_le_gainConstant mu K haj)
        (integral_nonneg fun _ => norm_nonneg _) (mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hell.le) _))
    _ = _ := by ring


end

end GlobalEmbedding.Offline
