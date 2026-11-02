import Probes.ActualPhaseEuclideanChart
import Probes.ActualInverseChartSampleJets

/-! The actual Euclidean adapted chart is chosen from the original low-order
open-domain data. Every later higher-order estimate is sampled, including at
compact parameter boundaries. Its inverse is estimated only from original
phase jets at the true inverse images of the sample. -/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def actualEuclideanPhaseSampleInverseJetCost (mu M Mj : ℝ) (j : ℕ) : ℝ :=
  actualInverseChartMajorant
    (slowInverseMajorant (actualEuclideanPhaseInverseJetCost mu M 0 0)
      (2^(j+2)*Mj) j) j

theorem actualEuclideanPhaseSampleInverseJetCost_nonneg
    {mu M Mj : ℝ} (hmu : 0 < mu) (hM : 0 ≤ M) (hMj : 0 ≤ Mj) (j : ℕ) :
    0 ≤ actualEuclideanPhaseSampleInverseJetCost mu M Mj j := by
  have hB := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
  apply zero_le_one.trans (actualInverseChartMajorant_one_le ?_ j)
  apply slowInverseMajorant_nonneg ?_ (by positivity)
  simp only [actualEuclideanPhaseInverseJetCost,actualInverseChartMajorant,
    slowInverseMajorant]
  positivity

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem actual_exists_native_euclidean_quantitative_phase_chart_sample_jets
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (rho : ℝ) (hrho : 0 < rho)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 rho))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 rho, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 rho, rho*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M rho) ⊆ a.source ∧
      a.source ⊆ ball z0 rho ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M rho)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ x ∈ a.source, ‖fderiv ℝ a x‖ ≤ 2*(1+2*M)) ∧
      (∀ i, 1 ≤ i → ∀ x ∈ a.source,
        ‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(i+2)*‖iteratedFDeriv ℝ (i+1) psi x‖) ∧
      (∀ (S : Set X), S ⊆ a.target → ∀ (j : ℕ) (weight Mj : ℝ),
        0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.symm '' S,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ S,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseSampleInverseJetCost mu M Mj j) := by
  obtain ⟨a,hi,ho,ha,hai,hp,hpi,ht,hpoint,hfirstA,_hforward,higher⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_pointwise_forward mu M hmu hM
      psi z0 rho hrho hpsi hspatial hfirst hsecond
  have hInv := actual_smooth_chart_fderiv_invertible a ha hai
  have hInvFirst : ∀ y ∈ a.target, ‖fderiv ℝ a.symm y‖ ≤
      actualEuclideanPhaseInverseJetCost mu M 0 0 := by
    intro y hy
    have h := higher 0 1 0 (by norm_num) le_rfl (by intro i hi hi0; omega)
      1 le_rfl le_rfl y hy
    simpa only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one] using h
  have hB : 0 ≤ actualEuclideanPhaseInverseJetCost mu M 0 0 := by
    have hb := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
    simp only [actualEuclideanPhaseInverseJetCost,actualInverseChartMajorant,
      slowInverseMajorant]
    positivity
  refine ⟨a,hi,ho,ha,hai,hp,hpi,ht,hfirstA,hpoint,?_⟩
  intro S hS j weight Mj hweight hMj hjet
  apply (actual_inverse_chart_slow_positive_jets_on_samples a ha hInv S hS j weight
    (actualEuclideanPhaseInverseJetCost mu M 0 0) (2^(j+2)*Mj)
    hweight hB (by positivity) ?_ ?_).2
  · rintro x ⟨y,hy,rfl⟩
    rw [← actual_inverse_chart_fderiv a ha hInv y (hS hy)]
    exact hInvFirst y (hS hy)
  · intro i hi hij x hx
    have hxsource : x ∈ a.source := by
      obtain ⟨y,hy,rfl⟩ := hx
      exact a.map_target (hS hy)
    calc
      _ ≤ weight^i*(2^(i+2)*‖iteratedFDeriv ℝ (i+1) psi x‖) :=
        mul_le_mul_of_nonneg_left (hpoint i hi x hxsource) (pow_nonneg hweight.le i)
      _ = 2^(i+2)*(weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖) := by ring
      _ ≤ 2^(i+2)*Mj := mul_le_mul_of_nonneg_left (hjet i hi hij x hx) (by positivity)
      _ ≤ 2^(j+2)*Mj := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) hMj

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart_sample_jets
