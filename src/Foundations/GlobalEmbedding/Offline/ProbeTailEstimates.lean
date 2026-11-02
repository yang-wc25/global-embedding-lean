import GlobalEmbedding.Offline.CoordinateStageSeries

/-!
# Actual probe series with the three quantitative tail rates

Source: main.tex, `prop:probes`, equations (8.2)–(8.4); DAG node
`probes-quantitative-repair-tail`. The same actual series and stage schedule
are used at every order. The prescribed one-step bounds remain the explicit
input supplied by the geometric iteration; this file proves their analytic
summation in the ORIGINAL componentwise coordinate norms.
-/

open Set Filter GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Offline

/-- The original full mixed componentwise norm. The first coordinate block
is the source and the second is the parameter. Words of lengths ZERO through
`a` and ZERO through `b` are both included. On smooth maps, Schwarz symmetry
identifies these words with the ordinary mixed multiindices. -/
noncomputable def paperMixedCoordinateCj {nx np q : ℕ} (a b : ℕ)
    (f : (Fin (nx + np) → ℝ) → Fin q → ℝ)
    (O S : Set (Fin (nx + np) → ℝ)) : ℝ≥0∞ :=
  ⨆ l : {l : List (Fin nx) // l.length ≤ a},
  ⨆ r : {r : List (Fin np) // r.length ≤ b}, ⨆ x : S, ⨆ c : Fin q,
    ENNReal.ofReal ‖paperCoordinatePartial
      (l.val.map (Fin.castAdd np) ++ r.val.map (Fin.natAdd nx)) (fun y ↦ f y c) O x‖

/-- The actual full mixed norm is bounded by the original full total-order
norm, with constant ONE. In particular the comparison retains pure source
derivatives and parameter order zero rather than only mixed top derivatives. -/
theorem paperMixedCoordinateCj_le_total
    {nx np q : ℕ} (a b : ℕ)
    (f : (Fin (nx + np) → ℝ) → Fin q → ℝ)
    (O S : Set (Fin (nx + np) → ℝ)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) :
    paperMixedCoordinateCj (nx := nx) (np := np) a b f O S ≤
      paperCoordinateCj (a + b) f O S := by
  refine iSup_le fun l ↦ iSup_le fun r ↦ iSup_le fun x ↦ iSup_le fun c ↦ ?_
  apply paper_coordinate_partial_le (a + b) f O S hO hSO hf
  simp only [List.length_append, List.length_map]
  exact Nat.add_le_add l.property r.property

/-- Each actual mixed partial is controlled by the full mixed norm. Taking
either word empty explicitly includes the value and pure derivatives. -/
theorem paper_mixed_partial_le
    {nx np q a b : ℕ}
    (f : (Fin (nx + np) → ℝ) → Fin q → ℝ)
    (O S : Set (Fin (nx + np) → ℝ))
    (l : List (Fin nx)) (r : List (Fin np))
    (hl : l.length ≤ a) (hr : r.length ≤ b) (x : S) (c : Fin q) :
    ENNReal.ofReal ‖paperCoordinatePartial
      (l.map (Fin.castAdd np) ++ r.map (Fin.natAdd nx)) (fun y ↦ f y c) O x‖ ≤
      paperMixedCoordinateCj (nx := nx) (np := np) a b f O S :=
  le_iSup_of_le ⟨l, hl⟩ (le_iSup_of_le ⟨r, hr⟩ (le_iSup_of_le x (le_iSup_of_le c le_rfl)))

/-- Sum an actual fixed-order probe estimate over the FULL repair sequence,
including every finite waiting block. Growing stage bounds independently give
smoothness of the SAME sum at all orders. The constant is the exact `2*C`.

No final tail bound or derivative convergence is an input: both are obtained
from the actual finite increments and their original paper norm bounds. -/
theorem paperCoordinateCj_probe_tail_le
    {n q : ℕ} (a : ℕ) {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop)
    {t C Cs p : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hC : 0 ≤ C) (hCs : 0 ≤ Cs) (hp : 1 ≤ p)
    (hstagebound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (Cs * iterationScale (t ^ (6 / 5 : ℝ)) j))
    (horderbound : ∀ j, paperCoordinateCj a (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ p)) :
    paperCoordinateCj a (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (2 * C * t ^ ((6 / 5 : ℝ) * p)) := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hτ : 0 < t ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos ht _
  have hτ1 : t ^ (6 / 5 : ℝ) < 1 := Real.rpow_lt_one ht.le ht1 (by norm_num)
  have hsum := smooth_series_on_of_paper_stage_bound hO f stage hf hstage hτ hτ1 hCs hstagebound
  let b (j : ℕ) := C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ p
  have hb (j : ℕ) : 0 ≤ b j :=
    mul_nonneg hC (Real.rpow_nonneg (iterationScale_pos hτ j).le _)
  have hbsum : Summable b :=
    (summable_iterationScale_power hτ hτ1 (by linarith : 0 < p)).mul_left C
  have hbudget : paperCoordinateCj a (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (∑' j, b j) := by
    apply paperCoordinateCj_le_of_jet_tendsto a hO (Subset.rfl)
      (fun J x ↦ ∑ j ∈ Finset.range J, f j x) (fun x ↦ ∑' j, f j x)
      (fun J ↦ ContDiffOn.sum fun j _hj ↦ hf j) hsum.1
      (fun J ↦ ∑ j ∈ Finset.range J, b j)
      (fun J ↦ Finset.sum_nonneg fun j _hj ↦ hb j) hbsum.hasSum.tendsto_sum_nat
    · intro J
      exact paperCoordinateCj_sum_le a hO (Subset.rfl) (Finset.range J) f
        (fun j _hj ↦ hf j) b (fun j _hj ↦ hb j) (fun j _hj ↦ horderbound j)
    · intro k _hk x hx
      have hlim := (hsum.2.2 k).tendsto_at hx
      simpa only [iteratedFDerivWithin_of_isOpen k hO hx] using hlim
  apply hbudget.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑' j, b j) = C * ∑' j, iterationScale (t ^ (6 / 5 : ℝ)) j ^ p := by
      simp only [b, tsum_mul_left]
    _ ≤ C * (2 * t ^ ((6 / 5 : ℝ) * p)) :=
      mul_le_mul_of_nonneg_left (tsum_iterationScale_next_power_le ht htsmall hp) hC
    _ = 2 * C * t ^ ((6 / 5 : ℝ) * p) := by ring

/-- The exact three full-total-order estimates behind equation (8.4), all
for one actual jointly smooth coordinate sum. The given estimates for orders
three, two and one include every lower order, by the definition of the original
componentwise Cj norm. They therefore retain parameter order zero as well.
-/
theorem probe_coordinate_tail_estimates
    {n q : ℕ} {O : Set (Fin n → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin n → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop)
    {t C Cs : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hstagebound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (Cs * iterationScale (t ^ (6 / 5 : ℝ)) j))
    (hthree : ∀ j, paperCoordinateCj 3 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (38 / 5 : ℝ)))
    (htwo : ∀ j, paperCoordinateCj 2 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (44 / 5 : ℝ)))
    (hone : ∀ j, paperCoordinateCj 1 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (10 : ℝ))) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' j, f j x) O ∧
    paperCoordinateCj 3 (fun x ↦ ∑' j, f j x) O O ≤ ENNReal.ofReal (2 * C * t ^ (228 / 25 : ℝ)) ∧
    paperCoordinateCj 2 (fun x ↦ ∑' j, f j x) O O ≤ ENNReal.ofReal (2 * C * t ^ (264 / 25 : ℝ)) ∧
    paperCoordinateCj 1 (fun x ↦ ∑' j, f j x) O O ≤ ENNReal.ofReal (2 * C * t ^ (12 : ℝ)) := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  refine ⟨(smooth_series_on_of_paper_stage_bound hO f stage hf hstage
    (Real.rpow_pos_of_pos ht _) (Real.rpow_lt_one ht.le ht1 (by norm_num))
    hCs hstagebound).1, ?_, ?_, ?_⟩
  · convert paperCoordinateCj_probe_tail_le 3 hO f stage hf hstage ht htsmall hC hCs
      (show (1 : ℝ) ≤ 38 / 5 by norm_num) hstagebound hthree using 1
    norm_num
  · convert paperCoordinateCj_probe_tail_le 2 hO f stage hf hstage ht htsmall hC hCs
      (show (1 : ℝ) ≤ 44 / 5 by norm_num) hstagebound htwo using 1
    norm_num
  · convert paperCoordinateCj_probe_tail_le 1 hO f stage hf hstage ht htsmall hC hCs
      (show (1 : ℝ) ≤ 10 by norm_num) hstagebound hone using 1
    norm_num

/-- Equation (8.4) in the actual full source/parameter mixed norms, for the
SAME jointly smooth sum. The third conclusion is slightly stronger than the
paper's parameter-derivative C0 bound, because it also includes the value.
No smoothness as a function of the external scale `t` is asserted. -/
theorem probe_mixed_tail_estimates
    {nx np q : ℕ} {O : Set (Fin (nx + np) → ℝ)} (hO : IsOpen O)
    (f : ℕ → (Fin (nx + np) → ℝ) → Fin q → ℝ) (stage : ℕ → ℕ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) O)
    (hstage : Tendsto stage atTop atTop)
    {t C Cs : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hstagebound : ∀ j, paperCoordinateCj (stage j / 2) (f j) O O ≤
      ENNReal.ofReal (Cs * iterationScale (t ^ (6 / 5 : ℝ)) j))
    (hthree : ∀ j, paperCoordinateCj 3 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (38 / 5 : ℝ)))
    (htwo : ∀ j, paperCoordinateCj 2 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (44 / 5 : ℝ)))
    (hone : ∀ j, paperCoordinateCj 1 (f j) O O ≤
      ENNReal.ofReal (C * iterationScale (t ^ (6 / 5 : ℝ)) j ^ (10 : ℝ))) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' j, f j x) O ∧
    paperMixedCoordinateCj (nx := nx) (np := np) 2 1 (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (2 * C * t ^ (228 / 25 : ℝ)) ∧
    paperMixedCoordinateCj (nx := nx) (np := np) 1 1 (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (2 * C * t ^ (264 / 25 : ℝ)) ∧
    paperMixedCoordinateCj (nx := nx) (np := np) 0 1 (fun x ↦ ∑' j, f j x) O O ≤
      ENNReal.ofReal (2 * C * t ^ (12 : ℝ)) := by
  have h := probe_coordinate_tail_estimates hO f stage hf hstage ht htsmall hC hCs
    hstagebound hthree htwo hone
  refine ⟨h.1, ?_, ?_, ?_⟩
  · exact (paperMixedCoordinateCj_le_total 2 1 _ O O hO (Subset.rfl) h.1).trans h.2.1
  · exact (paperMixedCoordinateCj_le_total 1 1 _ O O hO (Subset.rfl) h.1).trans h.2.2.1
  · exact (paperMixedCoordinateCj_le_total 0 1 _ O O hO (Subset.rfl) h.1).trans h.2.2.2

#print axioms paperMixedCoordinateCj_le_total
#print axioms paper_mixed_partial_le
#print axioms paperCoordinateCj_probe_tail_le
#print axioms probe_coordinate_tail_estimates
#print axioms probe_mixed_tail_estimates

end GlobalEmbedding.Offline
