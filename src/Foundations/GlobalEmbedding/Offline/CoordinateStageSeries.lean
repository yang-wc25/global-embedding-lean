import GlobalEmbedding.Offline.SmoothSeries
import GlobalEmbedding.Offline.IterationScales
import GlobalEmbedding.Paper.PaperCoordinateNormBridge

/-!
# The actual stage bounds imply one smooth coordinate sum

Source: `thm:repair`, main.tex lines 762–778; in particular the bound
`‖U_j‖_{C^{floor(k_j/2)}} ≤ ρ₁ t_j / 8` and `k_j → ∞`.

The hypothesis uses the repository's ORIGINAL extended componentwise
`paperCoordinateCj`, not a replacement norm. Only a fixed observation order
enters the finite-dimensional comparison constant. Thus the growing stage
does not introduce a growing constant into the summability argument.
The conclusion is the same pointwise sum at every derivative order.
-/

open Set Filter GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Offline

/-- Extract the actual scalar coefficient bound from the original norm.
All finiteness comes from the displayed finite upper bound; `toReal ⊤`
is never used to manufacture a finite estimate. -/
theorem coordinate_coefficient_le_of_paperCoordinateCj_le
    {n q j a : ℕ} {f : (Fin n → ℝ) → Fin q → ℝ}
    {O S : Set (Fin n → ℝ)} (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) {B : ℝ} (hB : 0 ≤ B)
    (hbound : paperCoordinateCj j f O S ≤ ENNReal.ofReal B)
    (ha : a ≤ j) {x : Fin n → ℝ} (hx : x ∈ S)
    (σ : Fin a → Fin n) (c : Fin q) :
    ‖iteratedFDeriv ℝ a f x (fun b ↦ Pi.single (σ b) 1) c‖ ≤ B := by
  have h := (coordinate_jet_coefficient_le_gauge f S ha ⟨x, hx⟩ σ c).trans
    ((paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf).symm.le.trans hbound)
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

/-- A bound on the original componentwise norm controls each fixed derivative.
The factor is `n^a`, depending on the observed derivative order `a`, not on
the potentially much larger controlled order `j`. -/
theorem iteratedFDeriv_le_of_paperCoordinateCj_le
    {n q j a : ℕ} {f : (Fin n → ℝ) → Fin q → ℝ}
    {O S : Set (Fin n → ℝ)} (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) {B : ℝ} (hB : 0 ≤ B)
    (hbound : paperCoordinateCj j f O S ≤ ENNReal.ofReal B)
    (ha : a ≤ j) {x : Fin n → ℝ} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ a f x‖ ≤ (n : ℝ) ^ a * B := by
  apply coordinate_multilinear_opNorm_le _ hB
  intro σ c
  exact coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO hf hB hbound ha hx σ c

/-- The paper's stage-order estimate supplies the actual eventual bound at
every fixed derivative order, without any higher-order entrance smallness.
The derivative on the open chart is the native `iteratedFDerivWithin`. -/
theorem eventually_iteratedFDerivWithin_le_of_stage_bound
    {n q : ℕ} {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop)
    {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j)) (a : ℕ) :
    ∀ᶠ j in atTop, ∀ x ∈ O,
      ‖iteratedFDerivWithin ℝ a (f j) O x‖ ≤
        ((n : ℝ) ^ a * C) * iterationScale t j := by
  have hlarge : ∀ᶠ j in atTop, 2 * a ≤ stage j :=
    hstage.eventually (eventually_ge_atTop (2 * a))
  filter_upwards [hlarge] with j hj x hx
  rw [iteratedFDerivWithin_of_isOpen a hO hx]
  have ha : a ≤ stage j / 2 := by omega
  simpa only [mul_assoc] using
    iteratedFDeriv_le_of_paperCoordinateCj_le hO (Subset.rfl) (hf j)
      (mul_nonneg hC (iterationScale_pos ht j).le) (hbound j) ha hx

/-- Stage control in the original paper norm yields a SINGLE smooth sum with
all actual derivative identities and uniform convergence on the open buffer.
Neither a common waiting time for every order nor bounded high derivatives
of the finitely many initial increments is assumed. Empty charts, zero source
dimension and zero target dimension are included. -/
theorem smooth_series_on_of_paper_stage_bound
    {n q : ℕ} {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop)
    {t C : ℝ} (ht : 0 < t) (ht1 : t < 1) (hC : 0 ≤ C)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j)) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' j, f j x) O ∧
    (∀ a x, x ∈ O →
      iteratedFDerivWithin ℝ a (fun y ↦ ∑' j, f j y) O x =
        ∑' j, iteratedFDerivWithin ℝ a (f j) O x) ∧
    (∀ a, TendstoUniformlyOn
      (fun J ↦ iteratedFDerivWithin ℝ a (fun x ↦ ∑ j ∈ Finset.range J, f j x) O)
      (iteratedFDerivWithin ℝ a (fun x ↦ ∑' j, f j x) O) atTop O) := by
  apply smooth_series_on_of_eventually hO f
    (fun a j ↦ ((n : ℝ) ^ a * C) * iterationScale t j) hf
  · intro a
    exact (summable_iterationScale ht ht1).mul_left _
  · exact eventually_iteratedFDerivWithin_le_of_stage_bound
      hO f stage hf hstage ht hC hbound

/-- Bounds in the original componentwise norm pass to a genuine smooth
derivative limit, with NO dimension or chart-count factor. This is a closed
inequality; a strict final budget must be reserved before taking the limit. -/
theorem paperCoordinateCj_le_of_jet_tendsto
    {n q : ℕ} (a : ℕ) {O S : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ)
    (g : (Fin n → ℝ) → Fin q → ℝ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O) (hg : ContDiffOn ℝ ∞ g O)
    (b : ℕ → ℝ) {B : ℝ} (hb : ∀ j, 0 ≤ b j)
    (hb_limit : Tendsto b atTop (𝓝 B))
    (hbound : ∀ j, paperCoordinateCj a (f j) O S ≤ ENNReal.ofReal (b j))
    (hD : ∀ k ≤ a, ∀ x ∈ S,
      Tendsto (fun j ↦ iteratedFDeriv ℝ k (f j) x) atTop
        (𝓝 (iteratedFDeriv ℝ k g x))) :
    paperCoordinateCj a g O S ≤ ENNReal.ofReal B := by
  rw [paperCoordinateCj_eq_coordinateJetGauge a g O S hO hSO hg]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  have hpoint := hD k.val (by omega) x x.property
  have heval := ((continuous_eval_const (fun b ↦ Pi.single (σ b) (1 : ℝ))).tendsto _).comp
    hpoint
  have hcomponent := ((continuous_apply c).tendsto _).comp heval
  apply le_of_tendsto_of_tendsto hcomponent.norm hb_limit
  exact Eventually.of_forall fun j ↦
    coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO (hf j)
      (hb j) (hbound j) (by omega) x.property σ c

/-- Finite sums retain the exact original componentwise budget. Smoothness
justifies differentiation of the actual sum; the scalar triangle inequality
is applied before the supremum, avoiding a number-of-charts factor. -/
theorem paperCoordinateCj_sum_le
    {n q : ℕ} (a : ℕ) {O S : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O)
    {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (hf : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) O)
    (b : ι → ℝ) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hbound : ∀ i ∈ s, paperCoordinateCj a (f i) O S ≤ ENNReal.ofReal (b i)) :
    paperCoordinateCj a (fun x ↦ ∑ i ∈ s, f i x) O S ≤
      ENNReal.ofReal (∑ i ∈ s, b i) := by
  rw [paperCoordinateCj_eq_coordinateJetGauge a _ O S hO hSO (ContDiffOn.sum hf)]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦
    ((hf i hi).contDiffAt (hO.mem_nhds (hSO x.property))).of_le (by simp))]
  simp only [sum_apply, Finset.sum_apply]
  apply norm_sum_le_of_le
  intro i hi
  exact coordinate_coefficient_le_of_paperCoordinateCj_le hO hSO (hf i hi)
    (hb i hi) (hbound i hi) (by omega) x.property σ c

/-- Increasing the controlled derivative order enlarges the ORIGINAL
componentwise norm. This uses its actual coefficient identification only on
the stated open smooth chart. -/
theorem paperCoordinateCj_mono_order
    {n q a b : ℕ} (hab : a ≤ b)
    {O S : Set (Fin n → ℝ)} (hO : IsOpen O) (hSO : S ⊆ O)
    (f : (Fin n → ℝ) → Fin q → ℝ) (hf : ContDiffOn ℝ ∞ f O) :
    paperCoordinateCj a f O S ≤ paperCoordinateCj b f O S := by
  rw [paperCoordinateCj_eq_coordinateJetGauge a f O S hO hSO hf,
    paperCoordinateCj_eq_coordinateJetGauge b f O S hO hSO hf]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  exact coordinate_jet_coefficient_le_gauge f S (by omega) x σ c

/-- The SAME stagewise smooth sum preserves every fixed low-order budget
already controlled at all stages. Its original componentwise norm is bounded
by the exact sum `C * ∑ t_j`, without a dimension or chart-count factor.
Consequently the strict reserve `∑ t_j < 1` can be used after this limit. -/
theorem paperCoordinateCj_tsum_le_of_stage_bound
    {n q : ℕ} (a : ℕ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 2 * a ≤ stage j)
    {t C : ℝ} (ht : 0 < t) (ht1 : t < 1) (hC : 0 ≤ C)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j)) :
    paperCoordinateCj a (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (C * ∑' j, iterationScale t j) := by
  have hsum := smooth_series_on_of_paper_stage_bound hO f stage hf hstage ht ht1 hC hbound
  have hb_nonneg (j : ℕ) : 0 ≤ C * iterationScale t j :=
    mul_nonneg hC (iterationScale_pos ht j).le
  have hsmall (j : ℕ) : paperCoordinateCj a (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j) :=
    (paperCoordinateCj_mono_order (by have := hmin j; omega) hO (Subset.rfl)
      (f j) (hf j)).trans (hbound j)
  have hbudget_limit : Tendsto
      (fun J ↦ ∑ j ∈ Finset.range J, C * iterationScale t j) atTop
      (𝓝 (C * ∑' j, iterationScale t j)) := by
    simpa only [tsum_mul_left] using
      ((summable_iterationScale ht ht1).mul_left C).hasSum.tendsto_sum_nat
  apply paperCoordinateCj_le_of_jet_tendsto a hO (Subset.rfl)
    (fun J x ↦ ∑ j ∈ Finset.range J, f j x) (fun x ↦ ∑' j, f j x)
    (fun J ↦ ContDiffOn.sum fun j _hj ↦ hf j) hsum.1
    (fun J ↦ ∑ j ∈ Finset.range J, C * iterationScale t j)
    (fun J ↦ Finset.sum_nonneg fun j _hj ↦ hb_nonneg j) hbudget_limit
  · intro J
    exact paperCoordinateCj_sum_le a hO (Subset.rfl) (Finset.range J) f
      (fun j _hj ↦ hf j) (fun j ↦ C * iterationScale t j)
      (fun j _hj ↦ hb_nonneg j) (fun j _hj ↦ hsmall j)
  · intro k _hk x hx
    have hlim := (hsum.2.2 k).tendsto_at hx
    simpa only [iteratedFDerivWithin_of_isOpen k hO hx] using hlim

/-- In particular the source's `ρ₁/8` C² increment reserve remains STRICT
for the actual smooth sum when `0<t₀≤1/32` and every stage is at least ten.
The same proof applies to every fixed order at most half the first stage. -/
theorem paperCoordinateCj_tsum_lt_of_stage_bound
    {n q : ℕ} (a : ℕ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 2 * a ≤ stage j)
    {t C : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hC : 0 < C)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j)) :
    paperCoordinateCj a (fun x ↦ ∑' j, f j x) O O < ENNReal.ofReal C := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  apply (paperCoordinateCj_tsum_le_of_stage_bound a hO f stage hf hstage hmin
    ht ht1 hC.le hbound).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hC).2
  exact (mul_lt_mul_of_pos_left (tsum_iterationScale_lt_one ht htsmall) hC).trans_eq
    (mul_one C)

/-- The same reserve works for the ORIGINAL finite-atlas MAX. All charts
share the actual stage sequence and scale, so no factor depending on the
number of charts occurs. The empty-atlas case is automatic. -/
theorem paperAtlasCj_tsum_lt_of_stage_bound
    {ι : Type*} [Fintype ι] {n q : ℕ} (a : ℕ)
    (O : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i))
    (f : ℕ → ι → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j i, ContDiffOn ℝ ∞ (f j i) (O i))
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 2 * a ≤ stage j)
    {t C : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hC : 0 < C)
    (hbound : ∀ j, paperAtlasCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (C * iterationScale t j)) :
    (∀ i, ContDiffOn ℝ ∞ (fun x ↦ ∑' j, f j i x) (O i)) ∧
    paperAtlasCj a (fun i x ↦ ∑' j, f j i x) O O < ENNReal.ofReal C := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hi (i : ι) (j : ℕ) :
      paperCoordinateCj (stage j / 2) (f j i) (O i) (O i) ≤
        ENNReal.ofReal (C * iterationScale t j) :=
    (le_iSup (fun i ↦ paperCoordinateCj (stage j / 2) (f j i) (O i) (O i)) i).trans
      (hbound j)
  constructor
  · intro i
    exact (smooth_series_on_of_paper_stage_bound (hO i) (fun j ↦ f j i) stage
      (fun j ↦ hf j i) hstage ht ht1 hC.le (hi i)).1
  · have hle : paperAtlasCj a (fun i x ↦ ∑' j, f j i x) O O ≤
        ENNReal.ofReal (C * ∑' j, iterationScale t j) := by
      apply iSup_le
      intro i
      exact paperCoordinateCj_tsum_le_of_stage_bound a (hO i) (fun j ↦ f j i) stage
        (fun j ↦ hf j i) hstage hmin ht ht1 hC.le (hi i)
    apply hle.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hC).2
    exact (mul_lt_mul_of_pos_left (tsum_iterationScale_lt_one ht htsmall) hC).trans_eq
      (mul_one C)

#print axioms coordinate_coefficient_le_of_paperCoordinateCj_le
#print axioms iteratedFDeriv_le_of_paperCoordinateCj_le
#print axioms eventually_iteratedFDerivWithin_le_of_stage_bound
#print axioms smooth_series_on_of_paper_stage_bound
#print axioms paperCoordinateCj_le_of_jet_tendsto
#print axioms paperCoordinateCj_sum_le
#print axioms paperCoordinateCj_mono_order
#print axioms paperCoordinateCj_tsum_le_of_stage_bound
#print axioms paperCoordinateCj_tsum_lt_of_stage_bound
#print axioms paperAtlasCj_tsum_lt_of_stage_bound

end GlobalEmbedding.Offline
