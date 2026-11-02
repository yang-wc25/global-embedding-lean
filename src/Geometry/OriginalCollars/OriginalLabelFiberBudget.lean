import OriginalCollars.OriginalLabelInteractionBudget

/-! Original labels need only their literal host assignment and a bound on
the actual finite fibers.  The bounded slots and their injection are
manufactured internally, then bound the actual interaction graph. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Classical
namespace GlobalEmbedding.Continuation.OriginalCollars

variable {Host Label : Type*} [Fintype Host] [Fintype Label]

def originalLabelHostSlot (host : Label → Host) (B : ℕ)
    (hB : ∀ i, Fintype.card {a : Label // host a = i} ≤ B) (a : Label) : Fin B :=
  dependentRefinementSlot B hB ⟨host a,⟨a,rfl⟩⟩

theorem originalLabelHostSlot_injective (host : Label → Host) (B : ℕ)
    (hB : ∀ i, Fintype.card {a : Label // host a = i} ≤ B) :
    Injective (fun a => (host a,originalLabelHostSlot host B hB a)) := by
  intro a b hab
  have h : (⟨host a,⟨a,rfl⟩⟩ : Sigma (fun i => {a : Label // host a = i})) =
      ⟨host b,⟨b,rfl⟩⟩ :=
    dependentRefinementSlot_injective B hB hab
  exact congrArg (fun x : Sigma (fun i => {a : Label // host a = i}) => x.2.val) h

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem originalLabelFiber_max_degree_add_one_le
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hBpos : 0 < B) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (hB : ∀ i, Fintype.card {a : Label // host a = i} ≤ B)
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) :
    Finset.univ.sup (tensorEnlargedSupportDegree S) + 1 ≤ (D+1)*B :=
  originalLabelInteraction_max_degree_add_one_le W S pull D B hBpos hD host
    (originalLabelHostSlot host B hB) (originalLabelHostSlot_injective host B hB) hSupport

theorem originalLabelFiber_closed_budget_le
    (W : Host → Set X) (S : Label → Set Y) (pull : Y → X)
    (D B : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (host : Label → Host) (hB : ∀ i, Fintype.card {a : Label // host a = i} ≤ B)
    (hSupport : ∀ a, S a ⊆ pull ⁻¹' W (host a)) :
    Finset.univ.sup (fun a => tensorEnlargedSupportDegree S a + 1) ≤ (D+1)*B :=
  originalLabelInteraction_closed_budget_le W S pull D B hD host
    (originalLabelHostSlot host B hB) (originalLabelHostSlot_injective host B hB) hSupport

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalLabelFiber_max_degree_add_one_le
#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalLabelFiber_closed_budget_le
