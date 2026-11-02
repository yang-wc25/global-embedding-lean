import Probes.ActualIncrementJointPrimaryError

/-! The actual finite sum of same-phase channel corrections keeps the bounded
subordinate multiplicity. The cap precedes the finite indexing type. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {N : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin N)

def actualJointCorrectionSumCost (N Bsub : ℕ) (coord : Fin N) (TP TQ : ℝ) : ℝ :=
  (Bsub : ℝ) * (‖incrementsFreeComplexCoordinate coord‖*TP +
    ‖Complex.I • incrementsFreeComplexCoordinate coord‖*TQ)

theorem actualJointCorrectionSumCost_nonneg (Bsub : ℕ) (coord : Fin N)
    {TP TQ : ℝ} (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ) :
    0 ≤ actualJointCorrectionSumCost N Bsub coord TP TQ := by
  unfold actualJointCorrectionSumCost
  positivity

theorem actual_joint_correction_sum_slow_jets (j Bsub : ℕ) (coord : Fin N)
    {A : Type*} [Fintype A] (hCard : Fintype.card A ≤ Bsub)
    (P Q : A → X → V) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (ell tau TP TQ : ℝ) (hell : 0 ≤ ell) (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ)
    (hPb : ∀ a, ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k (P a) z‖ ≤ TP*tau^2)
    (hQb : ∀ a, ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k (Q a) z‖ ≤ TQ*tau^2) :
    let C := fun z : X => ∑ a, (incrementsFreeComplexCoordinate coord (P a z) +
      Complex.I • incrementsFreeComplexCoordinate coord (Q a z))
    ContDiffOn ℝ ∞ C O ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^(k+1) * ‖iteratedFDeriv ℝ k C z‖ ≤
        actualJointCorrectionSumCost N Bsub coord TP TQ * tau^2 := by
  intro C
  let L := incrementsFreeComplexCoordinate coord
  let LI := Complex.I • L
  let term := fun a z => L (P a z)+LI (Q a z)
  have hterm (a : A) : ContDiffOn ℝ ∞ (term a) O :=
    (L.contDiff.comp_contDiffOn (hP a)).add (LI.contDiff.comp_contDiffOn (hQ a))
  refine ⟨ContDiffOn.sum (fun a _ => hterm a),?_⟩
  intro k hk z hz
  have hlin (f : X → V) (hf : ContDiffOn ℝ ∞ f O) (L : V →L[ℝ] ℂ) (T : ℝ)
      (hb : ell^(k+1)*‖iteratedFDeriv ℝ k f z‖ ≤ T*tau^2) :
      ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => L (f y)) z‖ ≤ ‖L‖*T*tau^2 := by
    have h := L.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds (hSO hz)))
      (by simp : (k : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell^(k+1)*(‖L‖*‖iteratedFDeriv ℝ k f z‖) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hell _)
      _ = ‖L‖*(ell^(k+1)*‖iteratedFDeriv ℝ k f z‖) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hb L.opNorm_nonneg).trans_eq (by ring)
  have htb (a : A) : ell^(k+1)*‖iteratedFDeriv ℝ k (term a) z‖ ≤
      (‖L‖*TP+‖LI‖*TQ)*tau^2 := by
    have hp := hlin (P a) (hP a) L TP (hPb a k hk z hz)
    have hq := hlin (Q a) (hQ a) LI TQ (hQb a k hk z hz)
    dsimp only [term]
    rw [fun_iteratedFDeriv_add_apply (f := fun y => L (P a y)) (g := fun y => LI (Q a y))
      (((L.contDiff.comp_contDiffOn (hP a)).contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
      (((LI.contDiff.comp_contDiffOn (hQ a)).contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))]
    have hh := mul_le_mul_of_nonneg_left (norm_add_le
      (iteratedFDeriv ℝ k (fun y => L (P a y)) z)
      (iteratedFDeriv ℝ k (fun y => LI (Q a y)) z)) (pow_nonneg hell (k+1))
    nlinarith
  change ell^(k+1)*‖iteratedFDeriv ℝ k (fun y => ∑ a, term a y) z‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply
    (fun a _ => ((hterm a).contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))]
  calc
    _ ≤ ell^(k+1) * ∑ a, ‖iteratedFDeriv ℝ k (term a) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hell _)
    _ = ∑ a, ell^(k+1)*‖iteratedFDeriv ℝ k (term a) z‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _a : A, (‖L‖*TP+‖LI‖*TQ)*tau^2 := Finset.sum_le_sum (fun a _ => htb a)
    _ = (Fintype.card A : ℝ)*(‖L‖*TP+‖LI‖*TQ)*tau^2 := by simp; ring
    _ ≤ (Bsub : ℝ)*(‖L‖*TP+‖LI‖*TQ)*tau^2 := by
      gcongr
    _ = _ := rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_correction_sum_slow_jets
