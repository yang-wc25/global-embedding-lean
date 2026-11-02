import Probes.ActualIncrementJointLeading

/-! Primitive tensor coefficient, actual input, cutoff, subordinate cutoff and
normal produce the original normalized free amplitude. The constant precedes
all fields and depends on no chart count. The argument is required positive
only at the genuine sampling points; no positivity of inactive extensions is
imposed. All derivatives are full joint derivatives. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

/-- The subordinate cutoff is inside the actual free amplitude. -/
theorem actual_subordinate_primary_free_jets_uniform
    (n : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X T V : Type*}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup T] [NormedSpace ℝ T]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
      (L : X → T →L[ℝ] ℝ) (input : X → T) (cutoff eta : X → ℝ) (normal : X → V)
      (hL : ContDiffOn ℝ ∞ L O) (hInput : ContDiffOn ℝ ∞ input O)
      (hCut : ContDiffOn ℝ ∞ cutoff O) (hEta : ContDiffOn ℝ ∞ eta O)
      (hNormal : ContDiffOn ℝ ∞ normal O)
      (ell tau : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau)
      (hReserve : ∀ z ∈ S, c ≤ L z (input z))
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ M)
      (hInputb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r input z‖ ≤ M)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r cutoff z‖ ≤ M)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r eta z‖ ≤ M)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r normal z‖ ≤ M),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w => (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (input w))))) • normal w) z‖ ≤ C*tau := by
  let H : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let B := max M (2^n*(‖H‖*M)*M)
  have hB : 0 ≤ B := hM.trans (le_max_left _ _)
  obtain ⟨Ca,hCa,hamp⟩ := increments_positive_reserve_amplitude_scaled_jets n c B hc hB
  refine ⟨|Real.sqrt 2| *Ca,mul_nonneg (abs_nonneg _) hCa,?_⟩
  intro X T V _ _ _ _ _ _ O S hO hSO L input cutoff eta normal hL hInput hCut hEta
    hNormal ell tau hell htau hReserve hLb hInputb hCutb hEtab hNormalb r hr z hz
  let cp := fun w => eta w*cutoff w
  have hcp : ContDiffOn ℝ ∞ cp O := hEta.mul hCut
  have hcpb : ∀ k ≤ n, ∀ w ∈ S, ell^k * ‖iteratedFDeriv ℝ k cp w‖ ≤ B := by
    intro k hk w hw
    have hh := slow_bilinear_jet_bound_norm H O hO eta cutoff hEta hCut k ell M M hell.le
      w (hSO hw) (fun i hi => hEtab i (hi.trans hk) w hw)
      (fun i hi => hCutb i (hi.trans hk) w hw)
    calc
      _ ≤ 2^k*(‖H‖*M)*M := hh
      _ ≤ 2^n*(‖H‖*M)*M := by gcongr <;> norm_num
      _ ≤ B := le_max_right _ _
  let v := fun w => (cp w*Real.sqrt (L w (input w))) • normal w
  have hvb : ell^r * ‖iteratedFDeriv ℝ r v z‖ ≤ Ca := hamp O S hO hSO L input cp normal
    hL hInput hcp hNormal ell hell hReserve
    (fun i hi w hw => (hLb i hi w hw).trans (le_max_left _ _))
    (fun i hi w hw => (hInputb i hi w hw).trans (le_max_left _ _)) hcpb
    (fun i hi w hw => (hNormalb i hi w hw).trans (le_max_left _ _)) r hr z hz
  have hv : ContDiffAt ℝ ∞ v z := increments_positive_reserve_amplitude_contDiffAt
    O hO L input cp normal hL hInput hcp hNormal (hSO hz) (hc.trans_le (hReserve z hz))
  have he : (fun w => (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (input w))))) • normal w) =
      fun w => (Real.sqrt 2*tau) • v w := by
    funext w
    dsimp only [v,cp]
    rw [smul_smul]
    congr 1
    ring
  rw [he, iteratedFDeriv_const_smul_apply' (hv.of_le (by simp : (r : ℕ∞ω) ≤ ∞)),
    norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg htau]
  calc
    ell^r*(|Real.sqrt 2| *tau*‖iteratedFDeriv ℝ r v z‖) =
      (|Real.sqrt 2| *tau)*(ell^r*‖iteratedFDeriv ℝ r v z‖) := by ring
    _ ≤ (|Real.sqrt 2| *tau)*Ca := mul_le_mul_of_nonneg_left hvb (by positivity)
    _ = _ := by ring

/-- Tame difference for the same subordinate free amplitude. -/
theorem actual_subordinate_primary_free_difference_jets_uniform
    (n : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X T V : Type*}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup T] [NormedSpace ℝ T]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
      (L : X → T →L[ℝ] ℝ) (input inputbar : X → T) (cutoff eta : X → ℝ) (normal : X → V)
      (hL : ContDiffOn ℝ ∞ L O) (hInput : ContDiffOn ℝ ∞ input O)
      (hInputbar : ContDiffOn ℝ ∞ inputbar O)
      (hCut : ContDiffOn ℝ ∞ cutoff O) (hEta : ContDiffOn ℝ ∞ eta O)
      (hNormal : ContDiffOn ℝ ∞ normal O)
      (ell tau Delta : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau) (hDelta : 0 ≤ Delta)
      (hReserve : ∀ z ∈ S, c ≤ L z (input z) ∧ c ≤ L z (inputbar z))
      (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ M)
      (hInputb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r input z‖ ≤ M)
      (hInputbarb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r inputbar z‖ ≤ M)
      (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r cutoff z‖ ≤ M)
      (hEtab : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r eta z‖ ≤ M)
      (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r normal z‖ ≤ M)
      (hDiff : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (fun w => input w-inputbar w) z‖ ≤ Delta),
    ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w => (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (input w))))) • normal w -
        (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (inputbar w))))) • normal w) z‖ ≤ C*tau*Delta := by
  let H : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let B := max M (2^n*(‖H‖*M)*M)
  have hB : 0 ≤ B := hM.trans (le_max_left _ _)
  obtain ⟨Ca,hCa,hamp⟩ := increments_positive_reserve_amplitude_difference_scaled_jets n c B hc hB
  refine ⟨|Real.sqrt 2| *Ca,mul_nonneg (abs_nonneg _) hCa,?_⟩
  intro X T V _ _ _ _ _ _ O S hO hSO L input inputbar cutoff eta normal hL hInput hInputbar hCut hEta
    hNormal ell tau Delta hell htau hDelta hReserve hLb hInputb hInputbarb hCutb hEtab hNormalb hDiff r hr z hz
  let cp := fun w => eta w*cutoff w
  have hcp : ContDiffOn ℝ ∞ cp O := hEta.mul hCut
  have hcpb : ∀ k ≤ n, ∀ w ∈ S, ell^k * ‖iteratedFDeriv ℝ k cp w‖ ≤ B := by
    intro k hk w hw
    have hh := slow_bilinear_jet_bound_norm H O hO eta cutoff hEta hCut k ell M M hell.le
      w (hSO hw) (fun i hi => hEtab i (hi.trans hk) w hw)
      (fun i hi => hCutb i (hi.trans hk) w hw)
    calc
      _ ≤ 2^k*(‖H‖*M)*M := hh
      _ ≤ 2^n*(‖H‖*M)*M := by gcongr <;> norm_num
      _ ≤ B := le_max_right _ _
  let vA := fun w => (cp w*Real.sqrt (L w (input w))) • normal w
  let vB := fun w => (cp w*Real.sqrt (L w (inputbar w))) • normal w
  let v := fun w => vA w-vB w
  have hvb : ell^r * ‖iteratedFDeriv ℝ r v z‖ ≤ Ca*Delta := hamp O S hO hSO L input inputbar cp normal
    hL hInput hInputbar hcp hNormal ell Delta hell hDelta hReserve
    (fun i hi w hw => (hLb i hi w hw).trans (le_max_left _ _))
    (fun i hi w hw => (hInputb i hi w hw).trans (le_max_left _ _))
    (fun i hi w hw => (hInputbarb i hi w hw).trans (le_max_left _ _)) hcpb
    (fun i hi w hw => (hNormalb i hi w hw).trans (le_max_left _ _)) hDiff r hr z hz
  have hvA : ContDiffAt ℝ ∞ vA z := increments_positive_reserve_amplitude_contDiffAt
    O hO L input cp normal hL hInput hcp hNormal (hSO hz) (hc.trans_le (hReserve z hz).1)
  have hvB : ContDiffAt ℝ ∞ vB z := increments_positive_reserve_amplitude_contDiffAt
    O hO L inputbar cp normal hL hInputbar hcp hNormal (hSO hz) (hc.trans_le (hReserve z hz).2)
  have hv : ContDiffAt ℝ ∞ v z := hvA.sub hvB
  have he : (fun w => (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (input w))))) • normal w -
      (eta w*(Real.sqrt 2*tau*(cutoff w*Real.sqrt (L w (inputbar w))))) • normal w) =
      fun w => (Real.sqrt 2*tau) • v w := by
    funext w
    dsimp only [v,vA,vB,cp]
    rw [smul_sub,smul_smul,smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [he, iteratedFDeriv_const_smul_apply' (hv.of_le (by simp : (r : ℕ∞ω) ≤ ∞)),
    norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg htau]
  calc
    ell^r*(|Real.sqrt 2| *tau*‖iteratedFDeriv ℝ r v z‖) =
      (|Real.sqrt 2| *tau)*(ell^r*‖iteratedFDeriv ℝ r v z‖) := by ring
    _ ≤ (|Real.sqrt 2| *tau)*(Ca*Delta) := mul_le_mul_of_nonneg_left hvb (by positivity)
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_subordinate_primary_free_jets_uniform

#print axioms GlobalEmbedding.Continuation.actual_subordinate_primary_free_difference_jets_uniform
