import Probes.ActualJointChartTransfer

/-! The base-two shift is retained through a FIXED reference chart. A
weighted (j+2)-jet of the actual map yields its actual adapted (j+2)-jet
with weight ell^j, without an artificial ell^-2 loss. The transition bound
is unweighted and belongs to the fixed reference geometry, not the new map.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem round3_fixed_chart_base_two_transfer
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j b : ℕ) (hb : b ≤ 2)
    (phi : X → Y) (f : Y → Z) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V)
    (hphi : ContDiffOn ℝ ∞ phi U) (hf : ContDiffOn ℝ ∞ f V)
    (hmap : MapsTo phi U V) (x : X) (hx : x ∈ U)
    (ell K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hfj : ∀ a ≤ j, ∀ c ≤ 2,
      ell^a*‖iteratedFDeriv ℝ (a+c) f (phi x)‖ ≤ K)
    (hphij : ∀ a, 1 ≤ a → a ≤ j+b → ‖iteratedFDeriv ℝ a phi x‖ ≤ T a) :
    ell^j*‖iteratedFDeriv ℝ (j+b) (f ∘ phi) x‖ ≤ actualFastChartTransferCost T (j+b)*K := by
  have hInput (i : ℕ) (hi : i ≤ j+b) : ‖iteratedFDeriv ℝ i f (phi x)‖ ≤ K/ell^j := by
    let a := i-2
    let c := i-a
    have haj : a ≤ j := by dsimp [a]; omega
    have hc2 : c ≤ 2 := by dsimp [c,a]; omega
    have he : a+c = i := by dsimp [c,a]; omega
    have hjet := hfj a haj c hc2
    rw [he] at hjet
    have hscale : ell^j ≤ ell^a := pow_le_pow_of_le_one hell.le hell1 haj
    apply (le_div_iff₀ (pow_pos hell j)).2
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans hjet
  have h := actual_fast_joint_chart_transfer T hT (j+b) phi f U V hU hV hphi hf hmap
    x hx 1 1 (K/ell^j) (by norm_num) le_rfl
    (fun i hi => by simpa only [one_pow,one_mul] using hInput i hi)
    (fun i hi hij => by simpa only [one_pow,one_mul] using hphij i hi hij)
  simp only [one_pow,one_mul] at h
  calc
    _ ≤ ell^j*(actualFastChartTransferCost T (j+b)*(K/ell^j)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hell.le j)
    _ = _ := by field_simp [(pow_pos hell j).ne']

#print axioms round3_fixed_chart_base_two_transfer
end GlobalEmbedding.Continuation
