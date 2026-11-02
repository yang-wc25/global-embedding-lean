import Probes.ActualPhaseEuclideanSampleChart

/-! Pointwise high-order certificates for one actual scalar phase chart.
The inverse derivatives read phase jets only at their true inverse samples. -/
noncomputable section
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

structure ActualPhaseSampleJetControls (mu Mb : ℝ) (phase : X → ℝ)
    (native : OpenPartialHomeomorph X X) : Prop where
  first : ∀ x ∈ native.source, ‖fderiv ℝ native x‖ ≤ 2*(1+2*Mb)
  higher : ∀ k, 1 ≤ k → ∀ x ∈ native.source,
    ‖iteratedFDeriv ℝ (k+1) native x‖ ≤ 2^(k+2)*‖iteratedFDeriv ℝ (k+1) phase x‖
  inverse : ∀ (S : Set X), S ⊆ native.target → ∀ (j : ℕ) (weight Mj : ℝ),
    0 < weight → 0 ≤ Mj →
    (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ native.symm '' S,
      weight^k*‖iteratedFDeriv ℝ (k+1) phase x‖ ≤ Mj) →
    ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
      weight^(k-1)*‖iteratedFDeriv ℝ k native.symm y‖ ≤
        actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j

theorem actual_sampled_phase_controls_of_bounds
    (mu Mb : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (phase : X → ℝ) (native : OpenPartialHomeomorph X X)
    (hSmooth : ContDiffOn ℝ ∞ native native.source)
    (hInverseSmooth : ContDiffOn ℝ ∞ native.symm native.target)
    (hFirst : ∀ x ∈ native.source, ‖fderiv ℝ native x‖ ≤ 2*(1+2*Mb))
    (hHigher : ∀ k, 1 ≤ k → ∀ x ∈ native.source,
      ‖iteratedFDeriv ℝ (k+1) native x‖ ≤ 2^(k+2)*‖iteratedFDeriv ℝ (k+1) phase x‖)
    (hInverseFirst : ∀ y ∈ native.target,
      ‖fderiv ℝ native.symm y‖ ≤ actualEuclideanPhaseInverseJetCost mu Mb 0 0) :
    ActualPhaseSampleJetControls mu Mb phase native := by
  have hInvertible := actual_smooth_chart_fderiv_invertible native hSmooth hInverseSmooth
  have hB : 0 ≤ actualEuclideanPhaseInverseJetCost mu Mb 0 0 := by
    have hb := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*Mb by positivity)
    simp only [actualEuclideanPhaseInverseJetCost,actualInverseChartMajorant,slowInverseMajorant]
    positivity
  refine ⟨hFirst,hHigher,?_⟩
  intro S hS j weight Mj hweight hMj hjet
  apply (actual_inverse_chart_slow_positive_jets_on_samples native hSmooth hInvertible S hS j weight
    (actualEuclideanPhaseInverseJetCost mu Mb 0 0) (2^(j+2)*Mj)
    hweight hB (by positivity) ?_ ?_).2
  · rintro x ⟨y,hy,rfl⟩
    rw [← actual_inverse_chart_fderiv native hSmooth hInvertible y (hS hy)]
    exact hInverseFirst y (hS hy)
  · intro k hk hkj x hx
    have hxsource : x ∈ native.source := by
      obtain ⟨y,hy,rfl⟩ := hx
      exact native.map_target (hS hy)
    calc
      _ ≤ weight^k*(2^(k+2)*‖iteratedFDeriv ℝ (k+1) phase x‖) :=
        mul_le_mul_of_nonneg_left (hHigher k hk x hxsource) (pow_nonneg hweight.le k)
      _ = 2^(k+2)*(weight^k*‖iteratedFDeriv ℝ (k+1) phase x‖) := by ring
      _ ≤ 2^(k+2)*Mj := mul_le_mul_of_nonneg_left (hjet k hk hkj x hx) (by positivity)
      _ ≤ 2^(j+2)*Mj := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) hMj

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_sampled_phase_controls_of_bounds
