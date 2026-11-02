import Probes.ActualInverseChartSampleJets
import Probes.Round3PreparedFiniteAssembly

/-!
Named positive-order inverse-chart profiles from the actual forward chart.
The input consists of forward jets, the first inverse reserve and a zeroth
coordinate bound. Higher inverse derivatives are conclusions on the same
samples. The k-th selected value reads the forward profile only through k.
-/

noncomputable section
open Set Function
open scoped ContDiff Classical
namespace GlobalEmbedding.Continuation

def round4InverseForwardPrefix (Forward : ℕ → ℝ) (j : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun i : Fin (j+1) => Forward i)

theorem round4InverseForwardPrefix_nonneg (Forward : ℕ → ℝ) (j : ℕ) :
    0 ≤ round4InverseForwardPrefix Forward j := round3PreparedFiniteMaximum_nonneg _

theorem round4InverseForwardPrefix_bound (Forward : ℕ → ℝ) (j i : ℕ) (hi : i ≤ j) :
    Forward i ≤ round4InverseForwardPrefix Forward j :=
  round3PreparedFiniteMaximum_bound (fun a : Fin (j+1) => Forward a) ⟨i,by omega⟩

theorem round4InverseForwardPrefix_congr {F G : ℕ → ℝ} (j : ℕ)
    (h : ∀ i ≤ j, F i = G i) :
    round4InverseForwardPrefix F j = round4InverseForwardPrefix G j := by
  unfold round4InverseForwardPrefix
  congr 1
  funext i
  exact h i (by omega)

def round4InverseChartProfile (b V : ℝ) (Forward : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then max 0 V else
    actualInverseChartMajorant
      (slowInverseMajorant b (round4InverseForwardPrefix Forward k) (k-1)) (k-1)

theorem round4InverseChartProfile_nonneg (b V : ℝ) (hb : 0 ≤ b)
    (Forward : ℕ → ℝ) (k : ℕ) :
    0 ≤ round4InverseChartProfile b V Forward k := by
  unfold round4InverseChartProfile
  split_ifs
  · exact le_max_left _ _
  · exact zero_le_one.trans (actualInverseChartMajorant_one_le
      (slowInverseMajorant_nonneg hb (round4InverseForwardPrefix_nonneg Forward k) (k-1)) (k-1))

theorem round4InverseChartProfile_congr_prefix (b V : ℝ) {F G : ℕ → ℝ}
    (k : ℕ) (h : ∀ i ≤ k, F i = G i) :
    round4InverseChartProfile b V F k = round4InverseChartProfile b V G k := by
  unfold round4InverseChartProfile
  rw [round4InverseForwardPrefix_congr k h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual inverse of the same smooth chart, with no compact maximum
of inverse higher derivatives and no enlarged evaluation domain. -/
theorem round4_actual_inverse_chart_finite_profile
    (a : OpenPartialHomeomorph E E)
    (ha : ContDiffOn ℝ ∞ a a.source) (hai : ContDiffOn ℝ ∞ a.symm a.target)
    (S : Set E) (hS : S ⊆ a.target)
    (ell b V : ℝ) (hell : 0 < ell) (hb : 0 ≤ b)
    (Forward : ℕ → ℝ)
    (hbase : ∀ x ∈ a.symm '' S, ‖(fderiv ℝ a x).inverse‖ ≤ b)
    (hvalue : ∀ y ∈ S, ‖a.symm y‖ ≤ V)
    (hforward : ∀ k, 1 ≤ k → ∀ x ∈ a.symm '' S,
      ell^(k-1)*‖iteratedFDeriv ℝ k a x‖ ≤ Forward k) :
    ∀ k y, y ∈ S → ell^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
      round4InverseChartProfile b V Forward k := by
  intro k y hy
  by_cases hk : k = 0
  · subst k
    simpa [round4InverseChartProfile] using (hvalue y hy).trans (le_max_right 0 V)
  · have hinv := actual_smooth_chart_fderiv_invertible a ha hai
    have hjet := (actual_inverse_chart_slow_positive_jets_on_samples a ha hinv S hS
      (k-1) ell b (round4InverseForwardPrefix Forward k) hell hb
      (round4InverseForwardPrefix_nonneg Forward k) hbase (by
        intro i hi hik x hx
        have h := hforward (i+1) (by omega) x hx
        simp only [Nat.add_sub_cancel] at h
        exact h.trans (round4InverseForwardPrefix_bound Forward k (i+1) (by omega)))).2
      k (by omega) (by omega) y hy
    simpa only [round4InverseChartProfile, ite_eq_right hk] using hjet

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_inverse_chart_finite_profile
#print axioms GlobalEmbedding.Continuation.round4InverseChartProfile_congr_prefix
