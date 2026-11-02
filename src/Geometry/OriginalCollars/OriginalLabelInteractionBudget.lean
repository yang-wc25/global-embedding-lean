import OriginalCollars.DependentRefinementBudget

/-!
# Actual original-label interaction degree from bounded pieces per host

Setup `setup:uniform` fixes the original enlarged-support degree and permits
only a bounded number of pieces per chart.  A literal host/slot injection
and support subordination therefore bound the actual label graph.  The
ambient projection permits joint parameter/source supports to be controlled
by their original source hosts.  No active-count or future output estimate
is supplied as a premise.

For an empty label type the supremum of closed-neighborhood cardinalities
is zero.  In contrast, maximum degree plus one is one, so its exact bound
requires a positive per-host slot bound (or an explicit maximum with one).
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology Classical
namespace GlobalEmbedding.Continuation.OriginalCollars

variable {Host Label X Y : Type*} [Fintype Host] [Fintype Label]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem originalLabelInteraction_degree_add_one_le
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (slot : Label → Fin B)
    (hInjective : Injective (fun a => (host a,slot a)))
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) (a : Label) :
    tensorEnlargedSupportDegree S a + 1 ≤ (D+1)*B := by
  let G := tensorEnlargedSupportGraph W
  let H := tensorEnlargedSupportGraph S
  let hosts := insert (host a) (G.neighborFinset (host a))
  let labels := insert a (H.neighborFinset a)
  let target := hosts.product (Finset.univ : Finset (Fin B))
  have hMap : Set.MapsTo (fun b => (host b,slot b)) labels target := by
    intro b hb
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    by_cases hba : host b = host a
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · apply Finset.mem_insert.mpr
      right
      apply (G.mem_neighborFinset (host a) (host b)).mpr
      obtain rfl | hb' := Finset.mem_insert.mp hb
      · exact (hba rfl).elim
      · have hAdj := (H.mem_neighborFinset a b).mp hb'
        obtain ⟨y,hya,hyb⟩ := hAdj.2
        exact ⟨Ne.symm hba,pull y,hSupport a hya,hSupport b hyb⟩
  have hCard : labels.card ≤ target.card :=
    Finset.card_le_card_of_injOn _ hMap (fun _ _ _ _ h => hInjective h)
  have hLabels : labels.card = tensorEnlargedSupportDegree S a + 1 := by
    rw [Finset.card_insert_of_notMem (H.notMem_neighborFinset_self a)]
    rfl
  have hHosts : hosts.card ≤ D+1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hD (host a)) 1)
  calc
    tensorEnlargedSupportDegree S a + 1 = labels.card := hLabels.symm
    _ ≤ target.card := hCard
    _ = hosts.card * B := by simp [target]
    _ ≤ (D+1)*B := Nat.mul_le_mul_right B hHosts

/-- Empty-safe actual closed-neighborhood budget, with no nonempty premise. -/
theorem originalLabelInteraction_closed_budget_le
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (slot : Label → Fin B)
    (hInjective : Injective (fun a => (host a,slot a)))
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) :
    (Finset.univ.sup (fun a => tensorEnlargedSupportDegree S a + 1)) ≤ (D+1)*B := by
  apply Finset.sup_le
  intro a _
  exact originalLabelInteraction_degree_add_one_le W S pull D B hD host slot hInjective hSupport a

/-- The conventional maximum-degree-plus-one budget has the same precise
bound whenever the original per-host bound is positive. -/
theorem originalLabelInteraction_max_degree_add_one_le
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hB : 0 < B) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (slot : Label → Fin B)
    (hInjective : Injective (fun a => (host a,slot a)))
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) :
    Finset.univ.sup (tensorEnlargedSupportDegree S) + 1 ≤ (D+1)*B := by
  have hPositive : 0 < (D+1)*B := Nat.mul_pos (by omega) hB
  have hMax : Finset.univ.sup (tensorEnlargedSupportDegree S) ≤ (D+1)*B-1 := by
    apply Finset.sup_le
    intro a _
    have h := originalLabelInteraction_degree_add_one_le W S pull D B hD host slot hInjective hSupport a
    omega
  omega

/-- Universal convention-preserving form, explicitly covering B=0 and an
empty label family.  No implicit nonempty-label assumption is introduced. -/
theorem originalLabelInteraction_max_degree_add_one_le_max
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (slot : Label → Fin B)
    (hInjective : Injective (fun a => (host a,slot a)))
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) :
    Finset.univ.sup (tensorEnlargedSupportDegree S) + 1 ≤ max 1 ((D+1)*B) := by
  have hPositive : 0 < max 1 ((D+1)*B) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hMax : Finset.univ.sup (tensorEnlargedSupportDegree S) ≤ max 1 ((D+1)*B)-1 := by
    apply Finset.sup_le
    intro a _
    have h := (originalLabelInteraction_degree_add_one_le W S pull D B hD host slot hInjective hSupport a).trans
      (le_max_right 1 ((D+1)*B))
    omega
  omega

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalLabelInteraction_max_degree_add_one_le
#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalLabelInteraction_closed_budget_le
