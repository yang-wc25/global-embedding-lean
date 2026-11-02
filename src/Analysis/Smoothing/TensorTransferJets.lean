import GlobalEmbedding.Offline.BufferedSmoothingJets

/-!
# Native all-order derivative costs for tensor frame transport

Source: the coordinate transformations in the tensor localization of (6.4).
The two varying frame factors in `Jᵀ H J`, the cutoff square, and the actual
source-chart transition are all differentiated. Constants are explicit finite
expressions in their provider sequences; none has an atlas or chart-count
argument. These are derivative estimates for the true product, not a supplied
error estimate in disguise.
-/

open Function Set Filter
open scoped ContDiff BigOperators Topology

namespace GlobalEmbedding.Offline

noncomputable section

/-- Native Leibniz convolution of two nonnegative derivative profiles. -/
def tensorProductJetConstant (A B : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * A l * B (j - l)

theorem tensorProductJetConstant_nonneg {A B : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (j : ℕ) :
    0 ≤ tensorProductJetConstant A B j :=
  Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hA l)) (hB _)

/-- The actual coefficient `chi² * J_left * J_right` costs this profile. -/
def tensorFrameWeightConstant (B J : ℕ → ℝ) : ℕ → ℝ :=
  tensorProductJetConstant (bufferedCutoffSquareConstant B)
    (tensorProductJetConstant J J)

theorem tensorFrameWeightConstant_nonneg {B J : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hJ : ∀ j, 0 ≤ J j) (j : ℕ) :
    0 ≤ tensorFrameWeightConstant B J j :=
  tensorProductJetConstant_nonneg (bufferedCutoffSquareConstant_nonneg hB)
    (tensorProductJetConstant_nonneg hJ hJ) j

/-- One entry of the tensor transport at derivative order `j`. -/
def tensorTransferCore (B T J : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * tensorFrameWeightConstant B J l *
    ((j - l).factorial : ℝ) * bufferedTransitionPrefix T (j - l) ^ (j - l)

theorem tensorTransferCore_nonneg {B T J : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (j : ℕ) :
    0 ≤ tensorTransferCore B T J j := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (tensorFrameWeightConstant_nonneg hB hJ l)) (by positivity))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT _)) _)

/-- Actual overlap multiplicity and the two finite tensor indices occur;
the number of atlas charts does not. -/
def tensorTransferConstant (n : ℕ) (B T J : ℕ → ℝ) (D j : ℕ) : ℝ :=
  (D : ℝ) * (n : ℝ) ^ 2 * ∑ k ∈ Finset.range (j + 1), tensorTransferCore B T J k

theorem tensorTransferConstant_nonneg (n : ℕ) {B T J : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (D j : ℕ) :
    0 ≤ tensorTransferConstant n B T J D j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (Finset.sum_nonneg fun k _ => tensorTransferCore_nonneg hB hT hJ k)

theorem tensorTransferConstant_mono (n : ℕ) {B T J : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j)
    (D : ℕ) {a c : ℕ} (hac : a ≤ c) :
    tensorTransferConstant n B T J D a ≤ tensorTransferConstant n B T J D c := by
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hac 1)
  · intro k _ _
    exact tensorTransferCore_nonneg hB hT hJ k

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking one literal coefficient cannot increase a native derivative norm. -/
theorem tensor_component_jet_le {q : ℕ} {f : E → Fin q → ℝ}
    {x : E} (hf : ContDiffAt ℝ ∞ f x) (k : Fin q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f y k) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  let L : (Fin q → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
    intro v
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v k
  have h := L.iteratedFDeriv_comp_left hf (i := j) (by simp)
  change ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ _
  rw [h]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Uniform bounds for all actual coefficients control the SAME native
vector jet in the Pi norm, with no extra target-dimension factor. -/
theorem tensor_jet_le_of_components {q : ℕ} {f : E → Fin q → ℝ}
    {x : E} (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ k, ‖iteratedFDeriv ℝ j (fun y => f y k) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ R := by
  apply ContinuousMultilinearMap.opNorm_le_bound hR
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR (Finset.prod_nonneg fun _ _ => norm_nonneg _))).mpr
  intro k
  let L : (Fin q → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hid := congrArg (fun P => P v) (L.iteratedFDeriv_comp_left hf (i := j) (by simp))
  change (iteratedFDeriv ℝ j (fun y => f y k) x) v = (iteratedFDeriv ℝ j f x v) k at hid
  rw [← hid]
  exact ((iteratedFDeriv ℝ j (fun y => f y k) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h k) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

/-- All-order product estimate for the same scalar functions. -/
theorem tensor_scalar_product_jet_le (A B : ℕ → ℝ)
    (hA : ∀ j, 0 ≤ A j) (_hB : ∀ j, 0 ≤ B j)
    {f g : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    {x : E} (hx : x ∈ O) (j : ℕ)
    (hF : ∀ k, ‖iteratedFDeriv ℝ k f x‖ ≤ A k)
    (hG : ∀ k, ‖iteratedFDeriv ℝ k g x‖ ≤ B k) :
    ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ tensorProductJetConstant A B j := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hO.uniqueDiffOn hx (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hF k) (by positivity))
    (hG (j - k)) (norm_nonneg _) (mul_nonneg (by positivity) (hA k))

/-- The true cutoff and BOTH frame factors have the explicit derivative cost. -/
theorem tensor_frame_weight_jet_le (B J : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hJ : ∀ j, 0 ≤ J j)
    {w l r : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hw : ContDiffOn ℝ ∞ w O) (hl : ContDiffOn ℝ ∞ l O) (hr : ContDiffOn ℝ ∞ r O)
    {x : E} (hx : x ∈ O) (j : ℕ)
    (hW : ∀ k, ‖iteratedFDeriv ℝ k w x‖ ≤ B k)
    (hL : ∀ k, ‖iteratedFDeriv ℝ k l x‖ ≤ J k)
    (hR : ∀ k, ‖iteratedFDeriv ℝ k r x‖ ≤ J k) :
    ‖iteratedFDeriv ℝ j (fun y => w y ^ 2 * (l y * r y)) x‖ ≤
      tensorFrameWeightConstant B J j := by
  apply tensor_scalar_product_jet_le _ _ (bufferedCutoffSquareConstant_nonneg hB)
    (tensorProductJetConstant_nonneg hJ hJ) hO (hw.pow 2) (hl.mul hr) hx j
  · intro k
    simpa only [one_pow, mul_one, bufferedCutoffSquareConstant] using
      norm_iteratedFDeriv_sq_le B hB 1 zero_le_one w O hO hw x hx
        (fun a => by simpa only [one_pow, mul_one] using hW a) k
  · intro k
    exact tensor_scalar_product_jet_le J J hJ hJ hO hl hr hx k hL hR

/-- Native derivative bound for one actual transported entry of a tensor
error. The error is composed with the true transition; both moving frame
coefficients and the cutoff square are differentiated by Leibniz. -/
theorem tensor_transferred_entry_jet_le (B T J : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j)
    {w l r g : E → ℝ} {t : E → E} {O U : Set E}
    (hO : IsOpen O) (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w O) (hl : ContDiffOn ℝ ∞ l O) (hr : ContDiffOn ℝ ∞ r O)
    (hg : ContDiffOn ℝ ∞ g U) (ht : ContDiffOn ℝ ∞ t O) (hmap : MapsTo t O U)
    {x : E} (hx : x ∈ O) (j : ℕ) (R : ℝ)
    (hW : ∀ k, ‖iteratedFDeriv ℝ k w x‖ ≤ B k)
    (hL : ∀ k, ‖iteratedFDeriv ℝ k l x‖ ≤ J k)
    (hR : ∀ k, ‖iteratedFDeriv ℝ k r x‖ ≤ J k)
    (hTder : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k t x‖ ≤ T k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k g (t x)‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun y => w y ^ 2 * (l y * r y) * g (t y)) x‖ ≤
      tensorTransferCore B T J j * R := by
  let W := fun y => w y ^ 2 * (l y * r y)
  have hWreg : ContDiffOn ℝ ∞ W O := (hw.pow 2).mul (hl.mul hr)
  have hgreg : ContDiffOn ℝ ∞ (g ∘ t) O := hg.comp ht hmap
  have hprod := norm_iteratedFDerivWithin_mul_le hWreg hgreg hO.uniqueDiffOn hx
    (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at hprod
  apply hprod.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * tensorFrameWeightConstant B J k *
        (((j - k).factorial : ℝ) * R * bufferedTransitionPrefix T (j - k) ^ (j - k)) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (tensor_frame_weight_jet_le B J hB hJ hO hw hl hr hx k hW hL hR) (by positivity))
        (buffered_composition_jet_le T hT hO hU ht hg hmap hx (j - k) R
          (fun a ha => hlocal a (ha.trans (Nat.sub_le _ _))) (fun a ha _ => hTder a ha))
        (norm_nonneg _)
        (mul_nonneg (by positivity) (tensorFrameWeightConstant_nonneg hB hJ k))
    _ = _ := by
      unfold tensorTransferCore
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Actual summation cost of the transported tensor entries. Inactive chart
labels have zero germs; the bound uses only their active cardinality `D`. -/
theorem tensor_finite_entry_sum_jet_le {ι : Type*} [Fintype ι] {n : ℕ}
    (f : ι → Fin n → Fin n → E → ℝ) (S : Finset ι) (D : ℕ) (hD : S.card ≤ D)
    (x : E) (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hreg : ∀ i r s, ContDiffAt ℝ ∞ (f i r s) x)
    (hzero : ∀ i, i ∉ S → ∀ r s, f i r s =ᶠ[𝓝 x] (fun _ => (0 : ℝ)))
    (hbound : ∀ i ∈ S, ∀ r s, ‖iteratedFDeriv ℝ j (f i r s) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ r, ∑ s, f i r s y) x‖ ≤
      (D : ℝ) * (n : ℝ) ^ 2 * C := by
  classical
  have hsum : iteratedFDeriv ℝ j (fun y => ∑ i, ∑ r, ∑ s, f i r s y) x =
      ∑ i, ∑ r, ∑ s, iteratedFDeriv ℝ j (f i r s) x := by
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (ContDiffAt.sum fun r _ => ContDiffAt.sum fun s _ => hreg i r s).of_le (by simp))]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedFDeriv_fun_sum_apply (fun r _ =>
      (ContDiffAt.sum fun s _ => hreg i r s).of_le (by simp))]
    apply Finset.sum_congr rfl
    intro r _
    exact iteratedFDeriv_fun_sum_apply (fun s _ => (hreg i r s).of_le (by simp))
  have hinactive (i : ι) (hi : i ∉ S) :
      (∑ r, ∑ s, iteratedFDeriv ℝ j (f i r s) x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s _
    simpa using ((hzero i hi r s).iteratedFDeriv ℝ j).eq_of_nhds
  rw [hsum, ← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hinactive i hi)]
  calc
    ‖∑ i ∈ S, ∑ r, ∑ s, iteratedFDeriv ℝ j (f i r s) x‖ ≤
        ∑ i ∈ S, ‖∑ r, ∑ s, iteratedFDeriv ℝ j (f i r s) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ∑ r, ∑ s, ‖iteratedFDeriv ℝ j (f i r s) x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
    _ ≤ ∑ _i ∈ S, ∑ _r : Fin n, ∑ _s : Fin n, C := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum fun s _ => hbound i hi r s
    _ = (S.card : ℝ) * (n : ℝ) ^ 2 * C := by simp; ring
    _ ≤ (D : ℝ) * (n : ℝ) ^ 2 * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (sq_nonneg _)

end

end GlobalEmbedding.Offline
