import IncrementsCompletion.OriginalSupportMultiplicity
import Repair.ReferenceHostColoring
import Mathlib.Data.Fintype.EquivFin

/-!
# A genuine interaction budget for dependent finite refinements

Source: `setup:uniform` and the phase preparation in `thm:repair`.
The original enlarged supports have degree at most `D`; each original
chart has at most `K` actual pieces.  This module manufactures the bounded
slots from those finite pieces.  No slot, coloring, refined degree or
pointwise count is supplied as an extra premise.

All estimates are independent of the number of original charts.  This is
a statement about refinements subordinate to the given original supports,
not a claim that arbitrary support systems have one common degree bound.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology BigOperators Classical

namespace GlobalEmbedding.Continuation.OriginalCollars

variable {Host : Type*} {Piece : Host → Type*}
  [Fintype Host] [∀ i, Fintype (Piece i)]

/-- The actual finite slot, chosen from the literal fiber cardinality. -/
def dependentRefinementSlot (K : ℕ) (hK : ∀ i, Fintype.card (Piece i) ≤ K)
    (a : Sigma Piece) : Fin K :=
  Fin.castLE (hK a.1) ((Fintype.equivFin (Piece a.1)) a.2)

theorem dependentRefinementSlot_injective
    (K : ℕ) (hK : ∀ i, Fintype.card (Piece i) ≤ K) :
    Injective (fun a : Sigma Piece => (a.1, dependentRefinementSlot K hK a)) := by
  intro a b hab
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  have hij : i = j := congrArg Prod.fst hab
  subst j
  have hs : dependentRefinementSlot K hK ⟨i, a⟩ =
      dependentRefinementSlot K hK ⟨i, b⟩ := congrArg Prod.snd hab
  have hf := Fin.castLE_injective (hK i) hs
  have hp := (Fintype.equivFin (Piece i)).injective hf
  exact congrArg (Sigma.mk i) hp

variable {X : Type*} [TopologicalSpace X]

/-- The neighbor budget is produced for the actual refined support graph.
The extra one counts the selected piece itself, including empty supports.
Thus no hidden bound on the total number of refinement pieces is used. -/
theorem dependentRefinement_degree_add_one_le
    (W : Host → Set X) (D K : ℕ)
    (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (hK : ∀ i, Fintype.card (Piece i) ≤ K)
    (S : Sigma Piece → Set X) (hS : ∀ a, S a ⊆ W a.1)
    (a : Sigma Piece) :
    tensorEnlargedSupportDegree S a + 1 ≤ (D + 1) * K := by
  classical
  let G := tensorEnlargedSupportGraph W
  let H := tensorEnlargedSupportGraph S
  let hosts := insert a.1 (G.neighborFinset a.1)
  let pieces := insert a (H.neighborFinset a)
  let target := hosts.product (Finset.univ : Finset (Fin K))
  have hmap : Set.MapsTo (fun b : Sigma Piece =>
      (b.1, dependentRefinementSlot K hK b)) pieces target := by
    intro b hb
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    by_cases hba : b.1 = a.1
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · apply Finset.mem_insert.mpr
      right
      apply (G.mem_neighborFinset a.1 b.1).mpr
      obtain rfl | hb' := Finset.mem_insert.mp hb
      · exact (hba rfl).elim
      · have hAdj := (H.mem_neighborFinset a b).mp hb'
        obtain ⟨x, hxa, hxb⟩ := hAdj.2
        exact ⟨Ne.symm hba, x, hS a hxa, hS b hxb⟩
  have hcount : pieces.card ≤ target.card :=
    Finset.card_le_card_of_injOn _ hmap
      (fun _ _ _ _ h => dependentRefinementSlot_injective K hK h)
  have hpieces : pieces.card = tensorEnlargedSupportDegree S a + 1 := by
    rw [Finset.card_insert_of_notMem (H.notMem_neighborFinset_self a)]
    rfl
  have hhosts : hosts.card ≤ D + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hD a.1) 1)
  calc
    tensorEnlargedSupportDegree S a + 1 = pieces.card := hpieces.symm
    _ ≤ target.card := hcount
    _ = hosts.card * K := by simp [target]
    _ ≤ (D + 1) * K := Nat.mul_le_mul_right K hhosts

/-- Proper bounded labels are generated from the actual finite fibers.
The original enlarged-support graph supplies the coloring. -/
theorem dependentRefinement_labels
    (W : Host → Set X) (D K : ℕ)
    (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (hK : ∀ i, Fintype.card (Piece i) ≤ K)
    (S : Sigma Piece → Set X) (hS : ∀ a, S a ⊆ W a.1) :
    ∃ label : Sigma Piece → ℕ,
      (∀ a, label a < (D + 2) * K) ∧
      (∀ a b, a ≠ b → (S a ∩ S b).Nonempty → label a ≠ label b) :=
  repair_reference_host_labels W D K hD Sigma.fst
    (dependentRefinementSlot K hK) (dependentRefinementSlot_injective K hK) S hS

/-- The actual cutoffs have the original local multiplicity, multiplied
only by the per-host piece bound.  All outside values remain untouched. -/
theorem dependentRefinement_cutoff_count
    (W : Host → Set X) (D K : ℕ)
    (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (hK : ∀ i, Fintype.card (Piece i) ≤ K)
    (chi : Sigma Piece → X → ℝ) (region : Set X)
    (hS : ∀ a x, x ∈ region → x ∈ tsupport (chi a) → x ∈ W a.1) :
    ∀ x ∈ region,
      (Finset.univ.filter (fun a => x ∈ tsupport (chi a))).card ≤ (D + 1) * K :=
  incrementsCompletion_original_cutoff_count_of_hosts W D K hD chi Sigma.fst
    (dependentRefinementSlot K hK) (dependentRefinementSlot_injective K hK) region hS

end GlobalEmbedding.Continuation.OriginalCollars

#print axioms GlobalEmbedding.Continuation.OriginalCollars.dependentRefinement_degree_add_one_le
#print axioms GlobalEmbedding.Continuation.OriginalCollars.dependentRefinement_labels
#print axioms GlobalEmbedding.Continuation.OriginalCollars.dependentRefinement_cutoff_count
