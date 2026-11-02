import GlobalEmbedding.Offline.CoordinateStageSeries
import Mathlib.Analysis.Real.Sqrt

/-!
# Initial scaling plus the full repair displacement budget

Source: `thm:repair`, equations (6.9) and the common-limit paragraph. The
actual initial map is `sqrt(1-delta₀²) • F₀`, not `F₀`. Its displacement
is included together with EVERY increment in the original coordinate Cj
norm. Only the displayed finite reference Cj bound is needed for this step.
-/

open Set Filter GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Offline

/-- The original smooth coordinate Cj norm respects a finite additive budget. -/
theorem paperCoordinateCj_add_le
    {n q : ℕ} (a : ℕ) {O S : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O)
    (f g : (Fin n → ℝ) → Fin q → ℝ)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : paperCoordinateCj a f O S ≤ ENNReal.ofReal A)
    (hgb : paperCoordinateCj a g O S ≤ ENNReal.ofReal B) :
    paperCoordinateCj a (fun x ↦ f x + g x) O S ≤ ENNReal.ofReal (A + B) := by
  rw [paperCoordinateCj_eq_coordinateJetGauge a _ O S hO hSO (hf.add hg)]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rw [fun_iteratedFDeriv_add_apply
    ((hf.contDiffAt (hO.mem_nhds (hSO x.property))).of_le (by simp))
    ((hg.contDiffAt (hO.mem_nhds (hSO x.property))).of_le (by simp))]
  change ‖iteratedFDeriv ℝ k.val f x (fun b ↦ Pi.single (σ b) 1) c +
    iteratedFDeriv ℝ k.val g x (fun b ↦ Pi.single (σ b) 1) c‖ ≤ A + B
  exact (norm_add_le _ _).trans (add_le_add
    (coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO hf hA hfb (by omega)
      x.property σ c)
    (coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO hg hB hgb (by omega)
      x.property σ c))

/-- Constant scalar multiplication preserves the actual componentwise norm
budget with the exact absolute scalar factor. Local smoothness is explicit. -/
theorem paperCoordinateCj_smul_le
    {n q : ℕ} (a : ℕ) {O S : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O)
    (f : (Fin n → ℝ) → Fin q → ℝ) (hf : ContDiffOn ℝ ∞ f O)
    (c : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hfb : paperCoordinateCj a f O S ≤ ENNReal.ofReal B) :
    paperCoordinateCj a (fun x ↦ c • f x) O S ≤ ENNReal.ofReal (|c| * B) := by
  have hcf : ContDiffOn ℝ ∞ (fun x ↦ c • f x) O :=
    (contDiffOn_const (c := c)).smul hf
  rw [paperCoordinateCj_eq_coordinateJetGauge a _ O S hO hSO hcf]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun d ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rw [iteratedFDeriv_const_smul_apply'
    ((hf.contDiffAt (hO.mem_nhds (hSO x.property))).of_le (by simp))]
  change ‖c • (iteratedFDeriv ℝ k.val f x (fun b ↦ Pi.single (σ b) 1) d)‖ ≤ |c| * B
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO hf hB hfb (by omega)
      x.property σ d) (abs_nonneg c)

/-- The exact initial scalar displacement is at most the squared defect
amplitude. This elementary bound even holds when the square-root argument
is negative, although the repair uses only `delta²<1`. -/
theorem initial_scaling_scalar_loss_le (delta : ℝ) :
    |Real.sqrt (1 - delta ^ 2) - 1| ≤ delta ^ 2 := by
  have hroot : Real.sqrt (1 - delta ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg delta])
  have hlower : 1 - delta ^ 2 ≤ Real.sqrt (1 - delta ^ 2) :=
    Real.le_sqrt_self_iff.mpr (by nlinarith [sq_nonneg delta])
  rw [abs_of_nonpos (sub_nonpos.mpr hroot)]
  linarith

/-- The source's initial scaling is controlled in the ORIGINAL Cj norm.
No initial term is silently dropped from the later displacement budget. -/
theorem initial_scaling_paperCoordinateCj_le
    {n q : ℕ} (a : ℕ) {O S : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O)
    (f : (Fin n → ℝ) → Fin q → ℝ) (hf : ContDiffOn ℝ ∞ f O)
    (delta : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hfb : paperCoordinateCj a f O S ≤ ENNReal.ofReal B) :
    paperCoordinateCj a (fun x ↦ Real.sqrt (1 - delta ^ 2) • f x - f x) O S ≤
      ENNReal.ofReal (delta ^ 2 * B) := by
  have heq : (fun x ↦ Real.sqrt (1 - delta ^ 2) • f x - f x) =
      (fun x ↦ (Real.sqrt (1 - delta ^ 2) - 1) • f x) := by
    funext x
    simp only [sub_smul, one_smul]
  rw [heq]
  exact (paperCoordinateCj_smul_le a hO hSO f hf _ hB hfb).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (initial_scaling_scalar_loss_le delta) hB))

/-- The actual initial map PLUS the whole stagewise increment series retains
a quantitative Cj reserve. The displayed choice of initial scale uses only
the finite reference bound `B`, not any uncontrolled higher derivatives.

The exact resulting upper bound is `5ρ/32`, leaving strict room below `ρ`.
For the repair application take `a=2`; stages at least ten satisfy `hmin`. -/
theorem repair_displacement_paperCoordinateCj_le
    {n q : ℕ} (a : ℕ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (F0 : (Fin n → ℝ) → Fin q → ℝ)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hF0 : ContDiffOn ℝ ∞ F0 O) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 2 * a ≤ stage j)
    {t ρ B : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hρ : 0 < ρ) (hB : 0 ≤ B) (htbudget : t ≤ ρ / (32 * (B + 1)))
    (hreference : paperCoordinateCj a F0 O O ≤ ENNReal.ofReal B)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal ((ρ / 8) * iterationScale t j)) :
    ContDiffOn ℝ ∞
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + ∑' j, f j x) O ∧
    paperCoordinateCj a
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + (∑' j, f j x) - F0 x) O O ≤
        ENNReal.ofReal (5 * ρ / 32) := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hsum := smooth_series_on_of_paper_stage_bound hO f stage hf hstage ht ht1
    (by positivity : 0 ≤ ρ / 8) hbound
  have htail := paperCoordinateCj_tsum_lt_of_stage_bound a hO f stage hf hstage hmin
    ht htsmall (by positivity : 0 < ρ / 8) hbound
  have hpower : (t ^ (10 : ℕ)) ^ 2 ≤ t := by
    rw [← pow_mul]
    exact pow_le_of_le_one ht.le ht1.le (by decide : (10 * 2 : ℕ) ≠ 0)
  have hscaled : t * (32 * (B + 1)) ≤ ρ :=
    (le_div_iff₀ (by positivity : 0 < 32 * (B + 1))).mp htbudget
  have hinitnum : (t ^ (10 : ℕ)) ^ 2 * B ≤ ρ / 32 := by
    have hmul := mul_le_mul_of_nonneg_right hpower hB
    nlinarith [ht.le]
  have hinit := (initial_scaling_paperCoordinateCj_le a hO (Subset.rfl) F0 hF0
    (t ^ (10 : ℕ)) hB hreference).trans (ENNReal.ofReal_le_ofReal hinitnum)
  have hscaledSmooth : ContDiffOn ℝ ∞
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x) O :=
    (contDiffOn_const (c := Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2))).smul hF0
  refine ⟨hscaledSmooth.add hsum.1, ?_⟩
  have heq :
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + (∑' j, f j x) - F0 x) =
      (fun x ↦ (Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x - F0 x) + ∑' j, f j x) := by
    funext x
    abel
  rw [heq]
  convert paperCoordinateCj_add_le a hO (Subset.rfl)
    (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x - F0 x)
    (fun x ↦ ∑' j, f j x) (hscaledSmooth.sub hF0) hsum.1
    (by positivity : 0 ≤ ρ / 32) (by positivity : 0 ≤ ρ / 8) hinit htail.le using 1
  congr 1
  ring

/-- The actual initialization and infinite series fit strictly inside the
prescribed Cj budget, with the reserve supplied by the preceding theorem. -/
theorem repair_displacement_paperCoordinateCj_lt
    {n q : ℕ} (a : ℕ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (F0 : (Fin n → ℝ) → Fin q → ℝ)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hF0 : ContDiffOn ℝ ∞ F0 O) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 2 * a ≤ stage j)
    {t ρ B : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hρ : 0 < ρ) (hB : 0 ≤ B) (htbudget : t ≤ ρ / (32 * (B + 1)))
    (hreference : paperCoordinateCj a F0 O O ≤ ENNReal.ofReal B)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal ((ρ / 8) * iterationScale t j)) :
    paperCoordinateCj a
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + (∑' j, f j x) - F0 x) O O <
        ENNReal.ofReal ρ := by
  apply (repair_displacement_paperCoordinateCj_le a hO F0 f stage hF0 hf hstage hmin
    ht htsmall hρ hB htbudget hreference hbound).2.trans_lt
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 (by linarith)

#print axioms paperCoordinateCj_add_le
#print axioms paperCoordinateCj_smul_le
#print axioms initial_scaling_scalar_loss_le
#print axioms initial_scaling_paperCoordinateCj_le
#print axioms repair_displacement_paperCoordinateCj_le
#print axioms repair_displacement_paperCoordinateCj_lt

end GlobalEmbedding.Offline
