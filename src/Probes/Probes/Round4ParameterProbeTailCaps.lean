import Smoothing.Round3RepairPrimitiveMeanData

/-! A single numerical entrance for the three actual repair tails in (8.4).
It reads the already constructed primitive displacement costs, before the
current map or any increment is chosen.  Stage zero is handled by the same
fixed constant, since waiting cannot absorb the zeroth stage power. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ENNReal BigOperators
namespace GlobalEmbedding.Continuation

def round4ParameterProbeTailConstant (cost : ℕ → Round3RepairPrimitiveCosts) : ℝ :=
  1 + (cost 0).Cmap 1 + (cost 0).Cmap 2 + (cost 0).Cmap 3

def round4ParameterProbeTailCap (cost : ℕ → Round3RepairPrimitiveCosts) (r : ℕ) : ℝ :=
  round4ParameterProbeTailConstant cost /
    (1 + (cost r).Cmap 1 + (cost r).Cmap 2 + (cost r).Cmap 3)

theorem round4ParameterProbeTailConstant_pos (cost : ℕ → Round3RepairPrimitiveCosts) :
    0 < round4ParameterProbeTailConstant cost := by
  unfold round4ParameterProbeTailConstant
  have := (cost 0).map_nonneg 1
  have := (cost 0).map_nonneg 2
  have := (cost 0).map_nonneg 3
  linarith

theorem round4ParameterProbeTailCap_pos (cost : ℕ → Round3RepairPrimitiveCosts) (r : ℕ) :
    0 < round4ParameterProbeTailCap cost r := by
  apply div_pos (round4ParameterProbeTailConstant_pos cost)
  have := (cost r).map_nonneg 1
  have := (cost r).map_nonneg 2
  have := (cost r).map_nonneg 3
  linarith

/-- One entrance absorbs all three finite observation costs on every stay
and advance of the same stage.  No proposed increment estimate is assumed. -/
theorem round4ParameterProbeTailCap_absorbs
    (cost : ℕ → Round3RepairPrimitiveCosts) (r a : ℕ) (ha : 1 ≤ a) (ha3 : a ≤ 3)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hcap : v ≤ round4ParameterProbeTailCap cost r) :
    (cost r).Cmap a * v^r ≤ round4ParameterProbeTailConstant cost := by
  have h0 (s : ℕ) := (cost s).map_nonneg 1
  have h1 (s : ℕ) := (cost s).map_nonneg 2
  have h2 (s : ℕ) := (cost s).map_nonneg 3
  have hsum : (cost r).Cmap a ≤
      1 + (cost r).Cmap 1 + (cost r).Cmap 2 + (cost r).Cmap 3 := by
    interval_cases a <;> linarith [h0 r,h1 r,h2 r]
  by_cases hr : r = 0
  · subst r
    simpa only [pow_zero,mul_one,round4ParameterProbeTailConstant] using hsum
  · have hpow : v^r ≤ v := by
      simpa only [pow_one] using pow_le_pow_of_le_one hv.le hv1 (Nat.one_le_iff_ne_zero.mpr hr)
    have hden : 0 < 1 + (cost r).Cmap 1 + (cost r).Cmap 2 + (cost r).Cmap 3 := by
      linarith [h0 r,h1 r,h2 r]
    have hbudget := (le_div_iff₀ hden).mp hcap
    calc
      _ ≤ (cost r).Cmap a * v := mul_le_mul_of_nonneg_left hpow ((cost r).map_nonneg a)
      _ ≤ (1 + (cost r).Cmap 1 + (cost r).Cmap 2 + (cost r).Cmap 3)*v :=
        mul_le_mul_of_nonneg_right hsum hv.le
      _ ≤ _ := by simpa only [mul_comm] using hbudget

/-- Unweight the exact original atlas maximum at any fixed order.  The
weighted input is the existing actual solver conclusion for that same U. -/
theorem round4ParameterProbe_unweight_original
    {ι : Type*} [Fintype ι] {n q : ℕ} (a j : ℕ) (haj : a ≤ j)
    (tau K : ℝ) (htau : 0 < tau)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin n → ℝ))
    (hfinite : paperAtlasWeighted 0 j tau f O S ≠ ⊤)
    (hbound : (paperAtlasWeighted 0 j tau f O S).toReal ≤ K) :
    paperAtlasCj a f O S ≤ ENNReal.ofReal (K / tau^a) := by
  have hterm : ENNReal.ofReal tau ^ a * paperAtlasCj a f O S ≤
      paperAtlasWeighted 0 j tau f O S := by
    simpa only [paperAtlasWeighted, Nat.add_zero] using
      (Finset.single_le_sum (fun i hi => (show (0 : ℝ≥0∞) ≤
        ENNReal.ofReal tau ^ i * paperAtlasCj (i+0) f O S from bot_le))
        (show a ∈ Finset.range (j+1) by simp; omega))
  have htermfinite := ne_top_of_le_ne_top hfinite hterm
  have hweight : ENNReal.ofReal tau ^ a ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.2 htau) a
  have hnorm : paperAtlasCj a f O S ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hweight] at htermfinite
    exact htermfinite rfl
  have hreal := (ENNReal.toReal_mono hfinite hterm).trans hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal htau.le] at hreal
  rw [← ENNReal.ofReal_toReal hnorm]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ (pow_pos htau a)).2 (by simpa only [mul_comm] using hreal)

theorem round4ParameterProbe_fixed_order_power
    {v C : ℝ} (hv : 0 < v) (r a : ℕ) :
    C*v^(10+r)*v^(6/5 : ℝ)/(v^(6/5 : ℝ))^a =
      (C*v^r)*v^((10 : ℝ)+(6/5 : ℝ)*(1-(a : ℝ))) := by
  have hpow : (v^(6/5 : ℝ))^a = v^((6/5 : ℝ)*(a : ℝ)) := by
    rw [Real.rpow_mul hv.le,Real.rpow_natCast]
  calc
    _ = C*(v^((10+r : ℕ) : ℝ)*v^(6/5 : ℝ)/v^((6/5 : ℝ)*(a : ℝ))) := by
      rw [Real.rpow_natCast,hpow]
      ring
    _ = C*v^(((10+r : ℕ) : ℝ)+(6/5 : ℝ)-(6/5 : ℝ)*(a : ℝ)) := by
      rw [← Real.rpow_add hv,← Real.rpow_sub hv]
    _ = C*(v^(r : ℝ)*v^((10 : ℝ)+(6/5 : ℝ)*(1-(a : ℝ)))) := by
      rw [← Real.rpow_add hv]
      congr 2
      push_cast
      ring
    _ = _ := by rw [Real.rpow_natCast]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbeTailCap_absorbs
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_unweight_original
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_fixed_order_power
