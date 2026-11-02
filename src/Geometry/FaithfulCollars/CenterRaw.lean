import Probes.Round4RefinementSquareCutoffs
import Smoothing.ParameterTransferBounds

/-!
# One raw plateau from a finite separated coordinate cover

This combines the actual uniformly bounded square partition of a separated
center family into ONE raw plateau.  The original chart index is retained;
there is no coordinate translation, change of norm domain, or enlargement
of a physical support.  The number of centers is bounded from the fixed
coordinate radius and buffer before this construction is used.
-/

noncomputable section
open GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def centerRaw (s : Finset E) (r : ℝ) : E → ℝ :=
  fun y => ∑ c : s, round4RefinementSquareCutoff E s r c y ^ 2

def centerRawCarrier (s : Finset E) (r : ℝ) : Set E :=
  ⋃ c : s, closedBall c.val (2*r)

def centerRawProfile (r : ℝ) (hr : 0 < r) (L : ℕ) (j : ℕ) : ℝ :=
  (L : ℝ) * tensorProductJetConstant (round4RefinementSquareProfile E r hr)
    (round4RefinementSquareProfile E r hr) j

theorem centerRawProfile_nonneg (r : ℝ) (hr : 0 < r) (L j : ℕ) :
    0 ≤ centerRawProfile E r hr L j :=
  mul_nonneg (Nat.cast_nonneg _) (tensorProductJetConstant_nonneg
    (round4RefinementSquareProfile_nonneg E r hr)
    (round4RefinementSquareProfile_nonneg E r hr) j)

theorem centerRawCarrier_compact (s : Finset E) (r : ℝ) :
    IsCompact (centerRawCarrier E s r) :=
  isCompact_iUnion fun _ => isCompact_closedBall _ _

theorem centerRaw_contDiff (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) :
    ContDiff ℝ ∞ (centerRaw E s r) := by
  apply ContDiff.sum
  intro c _
  exact ((round4_refinement_square_cutoffs E s r hr hsep).1 c).pow 2

theorem centerRaw_tsupport (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) :
    tsupport (centerRaw E s r) ⊆ centerRawCarrier E s r := by
  apply closure_minimal _ (centerRawCarrier_compact E s r).isClosed
  intro y hy
  by_contra hn
  have hz : ∀ c : s, round4RefinementSquareCutoff E s r c y = 0 := by
    intro c
    by_contra hc
    exact hn (mem_iUnion.mpr ⟨c,
      (round4_refinement_square_cutoffs E s r hr hsep).2.1 c (subset_tsupport _ hc)⟩)
  exact hy (by simp only [centerRaw, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero])

theorem centerRaw_one_on (s : Finset E) (r : ℝ) (hr : 0 < r) (K : Set E)
    (hcover : ∀ y ∈ K, ∃ c ∈ s, dist y c ≤ r) :
    ∀ y ∈ K, centerRaw E s r y = 1 := by
  obtain ⟨W, _, hKW, hW⟩ := round4_refinement_square_partition_near E s r hr K hcover
  exact fun y hy => hW y (hKW hy)

theorem centerRaw_jets (s : Finset E) (r : ℝ) (hr : 0 < r) (L : ℕ)
    (hcard : s.card ≤ L)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b)
    (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (centerRaw E s r) y‖ ≤ centerRawProfile E r hr L j := by
  let B := round4RefinementSquareProfile E r hr
  have hB : ∀ k, 0 ≤ B k := round4RefinementSquareProfile_nonneg E r hr
  have h := round4_refinement_square_cutoffs E s r hr hsep
  apply parameter_finite_sum_jet_le (fun c : s => fun z =>
    round4RefinementSquareCutoff E s r c z ^ 2) y Finset.univ L j
    (tensorProductJetConstant B B j)
    (by simpa only [Finset.card_univ, Fintype.card_coe] using hcard)
    (tensorProductJetConstant_nonneg hB hB j)
  · intro c _
    exact ((h.1 c).pow 2).contDiffAt
  · intro c hc
    exact False.elim (hc (Finset.mem_univ c))
  · intro c _
    simpa only [pow_two] using tensor_scalar_product_jet_le B B hB hB
      isOpen_univ (h.1 c).contDiffOn (h.1 c).contDiffOn (mem_univ y) j
      (fun k => h.2.2.2 c k y) (fun k => h.2.2.2 c k y)

end GlobalEmbedding.Continuation.FaithfulCollars
