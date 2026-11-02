import Repair.IncrementSignedNoncritical
import Repair.ReferenceSignedReserve

/-! The literal hierarchy normalizes every signed branch, including the
negative dominant term. The normalization coefficient is constructed;
no closeness estimate for an already assembled phase is an input. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
namespace GlobalEmbedding.Continuation

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem increment_four_signed_normalization
    (radius bound : ℝ) (hr : 0 < radius) (hb : 0 ≤ bound)
    (xi eta : E) (hxi : ‖xi‖ ≤ bound) {i j : ℕ} (hij : i < j) (branch : Fin 4) :
    let w := hierarchicalGoodWeight radius bound
    ∃ c : ℝ, 1 ≤ |c| ∧
      ‖c⁻¹ • (![w^j • eta+w^i • xi,w^j • eta-w^i • xi,
        -(w^j • eta)+w^i • xi,-(w^j • eta)-w^i • xi] branch)-eta‖ < radius := by
  intro w
  have hw : 1 < w := hierarchicalGoodWeight_gt_one hr hb
  have hp : 1 ≤ w^j := one_le_pow₀ hw.le
  have hc := repair_reference_hierarchy_normalized_close hr hb xi eta hxi hij
  have hn (v : E) : (-w^j)⁻¹ • (-v) = (w^j)⁻¹ • v := by
    simp only [inv_neg,neg_smul,smul_neg,neg_neg]
  fin_cases branch
  · refine ⟨w^j,by rwa [abs_of_nonneg (by linarith : 0 ≤ w^j)],?_⟩
    exact hc.1
  · refine ⟨w^j,by rwa [abs_of_nonneg (by linarith : 0 ≤ w^j)],?_⟩
    exact hc.2
  · refine ⟨-w^j,by simpa only [abs_neg,abs_of_nonneg (by linarith : 0 ≤ w^j)] using hp,?_⟩
    change ‖(-w^j)⁻¹ • (-(w^j • eta)+w^i • xi)-eta‖ < radius
    rw [show -(w^j • eta)+w^i • xi = -(w^j • eta-w^i • xi) by abel,hn]
    exact hc.2
  · refine ⟨-w^j,by simpa only [abs_neg,abs_of_nonneg (by linarith : 0 ≤ w^j)] using hp,?_⟩
    change ‖(-w^j)⁻¹ • (-(w^j • eta)-w^i • xi)-eta‖ < radius
    rw [show -(w^j • eta)-w^i • xi = -(w^j • eta+w^i • xi) by abel,hn]
    exact hc.1

theorem increment_doubled_normalization
    (radius weight : ℝ) (hr : 0 < radius) (hw : 1 ≤ weight) (xi : E)
    (branch : Fin 4) (hbranch : branch=0 ∨ branch=3) :
    ∃ c : ℝ, 1 ≤ |c| ∧
      ‖c⁻¹ • (![weight • xi+weight • xi,weight • xi-weight • xi,
        -(weight • xi)+weight • xi,-(weight • xi)-weight • xi] branch)-xi‖ < radius := by
  have hw0 : 0 < weight := by linarith
  have htwo : (2*weight) • xi = weight • xi+weight • xi := by rw [two_mul,add_smul]
  rcases hbranch with rfl | rfl
  · refine ⟨2*weight,by rw [abs_of_pos (mul_pos (by norm_num) hw0)]; linarith,?_⟩
    change ‖(2*weight)⁻¹ • (weight • xi+weight • xi)-xi‖ < radius
    rw [← htwo,smul_smul,inv_mul_cancel₀ (mul_ne_zero (by norm_num) hw0.ne'),one_smul,sub_self,norm_zero]
    exact hr
  · refine ⟨-(2*weight),by rw [abs_neg,abs_of_pos (mul_pos (by norm_num) hw0)]; linarith,?_⟩
    change ‖(-(2*weight))⁻¹ • (-(weight • xi)-weight • xi)-xi‖ < radius
    rw [show -(weight • xi)-weight • xi = -(weight • xi+weight • xi) by abel,
      inv_neg,neg_smul,smul_neg,neg_neg,← htwo,smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (by norm_num) hw0.ne'),one_smul,sub_self,norm_zero]
    exact hr
end Algebra
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_four_signed_normalization
#print axioms GlobalEmbedding.Continuation.increment_doubled_normalization
