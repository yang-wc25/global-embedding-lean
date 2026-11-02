import Probes.Round3PreparedSignedRefinementFactory
import Probes.ActualIncrementSecondaryPaddingBindings

/-! Finite preparation uses maxima for profiles and the actual local overlap
count for sums. The total number of prepared pieces is never inserted as a
multiplier in an analytic estimate. -/

noncomputable section
open Set Function
open scoped Classical BigOperators
namespace GlobalEmbedding.Continuation

def round3PreparedFiniteMaximum {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (insert 0 (Finset.univ.image f)).max' (Finset.insert_nonempty _ _)

theorem round3PreparedFiniteMaximum_nonneg {I : Type*} [Fintype I] (f : I → ℝ) :
    0 ≤ round3PreparedFiniteMaximum f :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem round3PreparedFiniteMaximum_bound {I : Type*} [Fintype I] (f : I → ℝ) (i : I) :
    f i ≤ round3PreparedFiniteMaximum f :=
  Finset.le_max' _ (f i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))

theorem round3_prepared_sigma_local_count
    {Parent X : Type*} [Fintype Parent]
    (Sub : Parent → Type*) [∀ i, Fintype (Sub i)]
    (parent : Parent → Set X) (carrier : (i : Parent) → Sub i → Set X)
    (hSupport : ∀ i a, carrier i a ⊆ parent i)
    (L R : ℕ) (x : X)
    (hParent : (Finset.univ.filter (fun i => x ∈ parent i)).card ≤ L)
    (hLocal : ∀ i, (Finset.univ.filter (fun a : Sub i => x ∈ carrier i a)).card ≤ R) :
    (Finset.univ.filter (fun a : Sigma Sub => x ∈ carrier a.1 a.2)).card ≤ L*R := by
  have hCard : (Finset.univ.filter (fun a : Sigma Sub => x ∈ carrier a.1 a.2)).card =
      ∑ i, (Finset.univ.filter (fun a : Sub i => x ∈ carrier i a)).card := by
    rw [show (Finset.univ.filter (fun a : Sigma Sub => x ∈ carrier a.1 a.2)).card =
      ∑ a : Sigma Sub, if x ∈ carrier a.1 a.2 then (1 : ℕ) else 0 from
        Finset.natCast_card_filter _ _]
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_boole _ _)
  rw [hCard]
  have hOne (i : Parent) : (Finset.univ.filter (fun a : Sub i => x ∈ carrier i a)).card ≤
      if x ∈ parent i then R else 0 := by
    split_ifs with hi
    · exact hLocal i
    · have he : (Finset.univ.filter (fun a : Sub i => x ∈ carrier i a)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hi (hSupport i a (Finset.mem_filter.mp ha).2)
      simp only [he,Finset.card_empty,le_refl]
  calc
    _ ≤ ∑ i : Parent, if x ∈ parent i then R else 0 := Finset.sum_le_sum (fun i _ => hOne i)
    _ = (Finset.univ.filter (fun i => x ∈ parent i)).card*R := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,smul_eq_mul]
    _ ≤ L*R := Nat.mul_le_mul_right R hParent

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3PreparedFiniteMaximum_bound
#print axioms GlobalEmbedding.Continuation.round3_prepared_sigma_local_count
