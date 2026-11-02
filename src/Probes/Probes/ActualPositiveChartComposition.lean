import Probes.ActualJointChartTransfer

/-! Positive-order composition with the correct slow weight. Centering the
outer map at the actual evaluation point removes any requirement on its
value. Thus a produced chart is controlled by its derivatives alone. -/

noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem actual_positive_joint_chart_composition
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) (hj : 1 ≤ j)
    (phi : X → Y) (f : Y → Z) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V)
    (hphi : ContDiffOn ℝ ∞ phi U) (hf : ContDiffOn ℝ ∞ f V)
    (hmap : MapsTo phi U V) (x : X) (hx : x ∈ U)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (hfjet : ∀ i, 1 ≤ i → i ≤ j →
      ell^(i-1)*‖iteratedFDeriv ℝ i f (phi x)‖ ≤ K)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j →
      ell^(i-1)*‖iteratedFDeriv ℝ i phi x‖ ≤ T i) :
    ell^(j-1)*‖iteratedFDeriv ℝ j (f ∘ phi) x‖ ≤ actualFastChartTransferCost T j*K := by
  let f0 : Y → Z := fun y => f y-f (phi x)
  have hf0 : ContDiffOn ℝ ∞ f0 V := hf.sub contDiffOn_const
  have hsub (i : ℕ) (hi : 1 ≤ i) (y : Y) (hy : y ∈ V) :
      iteratedFDeriv ℝ i f0 y = iteratedFDeriv ℝ i f y := by
    change iteratedFDeriv ℝ i (f-(fun _ => f (phi x))) y = _
    rw [iteratedFDeriv_sub_apply ((hf.contDiffAt (hV.mem_nhds hy)).of_le (by simp))
      contDiffAt_const,iteratedFDeriv_const_of_ne (by omega : i ≠ 0),Pi.zero_apply,sub_zero]
  have hpower (i : ℕ) (hi : 1 ≤ i) : ell^i = ell*ell^(i-1) := by
    rw [← pow_succ',Nat.sub_add_cancel hi]
  have hout : ∀ i ≤ j, ell^i*‖iteratedFDeriv ℝ i f0 (phi x)‖ ≤ ell*K := by
    intro i hij
    by_cases hi : i = 0
    · subst i
      simp only [norm_iteratedFDeriv_zero,f0,sub_self,norm_zero,mul_zero]
      exact mul_nonneg hell.le hK
    · rw [hsub i (by omega) _ (hmap hx),hpower i (by omega),mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfjet i (by omega) hij) hell.le
  have h := actual_fast_joint_chart_transfer T hT j phi f0 U V hU hV hphi hf0 hmap
    x hx ell ell (ell*K) hell le_rfl hout hphijet
  have heq : iteratedFDeriv ℝ j (f0 ∘ phi) x = iteratedFDeriv ℝ j (f ∘ phi) x := by
    change iteratedFDeriv ℝ j ((f ∘ phi)-(fun _ => f (phi x))) x = _
    rw [iteratedFDeriv_sub_apply (((hf.comp hphi hmap).contDiffAt (hU.mem_nhds hx)).of_le (by simp))
      contDiffAt_const,iteratedFDeriv_const_of_ne (by omega : j ≠ 0),Pi.zero_apply,sub_zero]
  rw [heq,hpower j hj,mul_assoc] at h
  apply (mul_le_mul_iff_right₀ hell).mp
  exact h.trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_positive_joint_chart_composition
