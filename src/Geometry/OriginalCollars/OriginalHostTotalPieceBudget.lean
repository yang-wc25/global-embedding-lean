import OriginalCollars.OriginalLabelFiberBudget

/-!
# Total refined pieces at one original owner

This counts all pieces at an owner, not only those meeting a point.
Original labels have bounded fibers over their original hosts; their
supports and the owner's parent support are subordinate to those hosts.
An actual center of a nonempty refinement witnesses an intersection, so
only labels on the owner's closed host-neighborhood can contribute.
Combining this proved label count with the actual model packing bound
gives (D+1)*B*L total pieces without a global chart or label factor.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology Classical BigOperators
namespace GlobalEmbedding.Continuation.OriginalCollars

variable {Host Label X Y : Type*} [Fintype Host] [Fintype Label]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem originalLabelFiber_host_intersection_count
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (hFiber : ∀ i, Fintype.card {a : Label // host a = i} ≤ B)
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a))
    (i : Host) (T : Set Y) (hParent : T ⊆ pull ⁻¹' W i) :
    (Finset.univ.filter (fun a => (S a ∩ T).Nonempty)).card ≤ (D+1)*B := by
  let G := tensorEnlargedSupportGraph W
  let hosts := insert i (G.neighborFinset i)
  let labels := Finset.univ.filter (fun a => (S a ∩ T).Nonempty)
  let slot := originalLabelHostSlot host B hFiber
  let target := hosts.product (Finset.univ : Finset (Fin B))
  have hMap : Set.MapsTo (fun a => (host a,slot a)) labels target := by
    intro a ha
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    by_cases hi : host a = i
    · exact Finset.mem_insert.mpr (Or.inl hi)
    · apply Finset.mem_insert.mpr
      right
      apply (G.mem_neighborFinset i (host a)).mpr
      obtain ⟨y,hys,hyt⟩ := (Finset.mem_filter.mp ha).2
      exact ⟨Ne.symm hi,pull y,hParent hyt,hSupport a hys⟩
  have hCard : labels.card ≤ target.card :=
    Finset.card_le_card_of_injOn _ hMap
      (fun _ _ _ _ h => originalLabelHostSlot_injective host B hFiber h)
  have hHosts : hosts.card ≤ D+1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hD i) 1)
  calc
    (Finset.univ.filter (fun a => (S a ∩ T).Nonempty)).card = labels.card := rfl
    _ ≤ target.card := hCard
    _ = hosts.card * B := by simp [target]
    _ ≤ (D+1)*B := Nat.mul_le_mul_right B hHosts

theorem originalLabelFiber_nonempty_piece_count
    {Z : Type*} (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (hFiber : ∀ i, Fintype.card {a : Label // host a = i} ≤ B)
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a))
    (i : Host) (T : Set Y) (hParent : T ⊆ pull ⁻¹' W i)
    (s : Label → Finset Z)
    (hActive : ∀ a, (s a).Nonempty → (S a ∩ T).Nonempty) :
    (Finset.univ.filter (fun a => (s a).Nonempty)).card ≤ (D+1)*B := by
  apply (Finset.card_le_card ?_).trans
    (originalLabelFiber_host_intersection_count W S pull D B hD host hFiber hSupport i T hParent)
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hActive a (Finset.mem_filter.mp ha).2⟩

/-- The local packing budget is attached to each actual finite center set.
An original host assignment and its finite fiber bound, not the total
number of original labels, control the full sum at one owner. -/
theorem originalLabelFiber_total_pieces_le
    {Z : Type*} (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B L : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (hFiber : ∀ i, Fintype.card {a : Label // host a = i} ≤ B)
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a))
    (i : Host) (T : Set Y) (hParent : T ⊆ pull ⁻¹' W i)
    (s : Label → Finset Z)
    (hActive : ∀ a, (s a).Nonempty → (S a ∩ T).Nonempty)
    (hCard : ∀ a, (s a).card ≤ L) :
    (∑ a, (s a).card) ≤ (D+1)*B*L := by
  have hOne (a : Label) : (s a).card ≤ if (s a).Nonempty then L else 0 := by
    split_ifs with h
    · exact hCard a
    · have he : s a = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [he,Finset.card_empty,le_refl]
  calc
    (∑ a, (s a).card) ≤ ∑ a : Label, if (s a).Nonempty then L else 0 :=
      Finset.sum_le_sum (fun a _ => hOne a)
    _ = (Finset.univ.filter (fun a => (s a).Nonempty)).card*L := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,smul_eq_mul]
    _ ≤ (D+1)*B*L := Nat.mul_le_mul_right L
      (originalLabelFiber_nonempty_piece_count W S pull D B hD host hFiber hSupport
        i T hParent s hActive)

end GlobalEmbedding.Continuation.OriginalCollars

#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalLabelFiber_total_pieces_le
