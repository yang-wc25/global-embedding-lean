import FaithfulIncrements.GivenFiniteEnvelope

/-!
# A common bounded-input envelope, selected before the actual datum

The entrance reads only the prescribed finite current-scale prefix. A
separate common bound for the unit-scale higher inputs controls all output
orders uniformly on a bounded set of data. It does not restrict the
entrance threshold, and no extended norm is replaced by an unguarded toReal.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open FaithfulIncrements

/-- A numerical common profile, independent of every actual atlas and map. -/
def boundedGivenEnvelope (J : ℕ) (allowed tail : ℕ → ℝ) : ℕ → ℝ :=
  repairEntranceFiniteProfile J allowed tail

theorem boundedGivenEnvelope_prefix (J : ℕ) (allowed tail : ℕ → ℝ)
    (j : ℕ) (hj : j ≤ J) : boundedGivenEnvelope J allowed tail j = allowed j :=
  repairEntranceFiniteProfile_prefix J allowed tail j hj

theorem boundedGivenEnvelope_nonneg (J : ℕ) (allowed tail : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J → 0 ≤ allowed j) (hTail : ∀ j, 0 ≤ tail j) :
    ∀ j, 0 ≤ boundedGivenEnvelope J allowed tail j :=
  repairEntranceFiniteProfile_nonneg J allowed tail hAllowed hTail

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The actual datum-dependent completion is dominated by the numerical
common completion on any prescribed bounded set of the higher inputs. -/
theorem actualGivenEnvelope_le_bounded
    (Data : IncrementsOriginalNativeData n d N M P)
    (J : ℕ) (allowed tail : ℕ → ℝ)
    (hTail : ∀ j, J < j → (actualOriginalGivenInputProfile Data j 1).toReal ≤ tail j)
    (j : ℕ) : actualGivenEnvelope Data J allowed j ≤ boundedGivenEnvelope J allowed tail j := by
  by_cases hj : j ≤ J
  · rw [actualGivenEnvelope_prefix Data J allowed j hj,
      boundedGivenEnvelope_prefix J allowed tail j hj]
  · change repairEntranceFiniteProfile J allowed _ j ≤ repairEntranceFiniteProfile J allowed tail j
    simp only [repairEntranceFiniteProfile, if_neg hj]
    exact hTail j (Nat.lt_of_not_ge hj)

/-- All scales consume the same common high-input bound. Only the finite
prefix is tested at the current scale; the original norm domains are unchanged. -/
theorem boundedGivenEnvelope_current_scale
    (Data : IncrementsOriginalNativeData n d N M P)
    (J : ℕ) (allowed tail : ℕ → ℝ)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (hTail : ∀ j, J < j → (actualOriginalGivenInputProfile Data j 1).toReal ≤ tail j)
    (ell : ℝ) (hell : ell ≤ 1)
    (hPrefix : ∀ j, j ≤ J → (actualOriginalGivenInputProfile Data j ell).toReal ≤ allowed j)
    (j : ℕ) : actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ boundedGivenEnvelope J allowed tail j := by
  obtain ⟨hFiniteEll,hBound⟩ := actualGivenEnvelope_current_scale Data J allowed hFinite ell hell hPrefix j
  exact ⟨hFiniteEll,hBound.trans (actualGivenEnvelope_le_bounded Data J allowed tail hTail j)⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.boundedGivenEnvelope_current_scale
