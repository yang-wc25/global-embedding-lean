import Probes.Round4UniformFreeNormalCoordinate
import Mathlib.Data.Sym.Card

/-!
The original ambient dimension bound supplies the strict rank deficit for
the actual first frame and the once-sorted transverse second-form frame.
No independent rank-deficit assumption is added to the geometric producer.
-/

noncomputable section
namespace GlobalEmbedding.Continuation

theorem round4_sorted_transverse_card_le (m : ℕ) :
    Fintype.card {p : Fin m × Fin m // p.1 ≤ p.2} ≤ (m+1).choose 2 := by
  classical
  let f : {p : Fin m × Fin m // p.1 ≤ p.2} → Sym2 (Fin m) :=
    fun p => Sym2.mk p.val.1 p.val.2
  have hf : Function.Injective f := by
    rintro ⟨⟨a,b⟩, hab⟩ ⟨⟨c,d⟩, hcd⟩ h
    change Sym2.mk a b = Sym2.mk c d at h
    rcases Sym2.eq_iff.mp h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact Subtype.ext (Prod.ext hac hbd)
    · subst d
      subst c
      have hab' : a = b := le_antisymm hab hcd
      subst b
      rfl
  simpa only [Sym2.card, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem round4_original_normal_rank_deficit (m N : ℕ)
    (hdim : (m+1)*(m+2)/2 < N) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) +
      Module.finrank ℝ (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) < N := by
  rw [finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_fin]
  have hcard := round4_sorted_transverse_card_le m
  have hchoose : (m+1) + (m+1).choose 2 = (m+2).choose 2 := by
    simpa only [Nat.choose_one_right] using (Nat.choose_succ_succ' (m+1) 1).symm
  have htwo : (m+2).choose 2 = (m+1)*(m+2)/2 := by
    rw [Nat.choose_two_right]
    rw [show m+2-1 = m+1 by omega]
    congr 1
    exact Nat.mul_comm _ _
  exact (Nat.add_le_add_left hcard (m+1)).trans_lt (by rwa [hchoose, htwo])

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_normal_rank_deficit
