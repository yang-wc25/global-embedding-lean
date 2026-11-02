import Repair.EntrancePointwiseComposition

/-!
# Composition costs that read only positive coordinate jets

The existing actual positive-composition theorem centers the outer map at
the actual image point, proves its zeroth jet is zero, and calls the actual
fast chart transfer.  Here both numerical zeroth slots are explicitly zero.
The resulting cost is invariant under changes to coordinate values and to
all input-profile entries outside the positive prefix being observed.

No chart, sample, map, or differentiation domain is changed.  The centered
map is only the existing proof's internal estimate; the output is the true
composition at the true point.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

/-- The zero slot is not a coordinate-value budget. -/
def incrementsCompletionPositiveSlots (P : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else P k

theorem incrementsCompletionPositiveSlots_zero (P : ℕ → ℝ) :
    incrementsCompletionPositiveSlots P 0 = 0 := by
  simp [incrementsCompletionPositiveSlots]

theorem incrementsCompletionPositiveSlots_of_pos (P : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    incrementsCompletionPositiveSlots P k = P k := by
  simp [incrementsCompletionPositiveSlots,show k ≠ 0 by omega]

theorem incrementsCompletionPositiveSlots_nonneg
    (P : ℕ → ℝ) (hP : ∀ k, 1 ≤ k → 0 ≤ P k) (k : ℕ) :
    0 ≤ incrementsCompletionPositiveSlots P k := by
  by_cases hk : k = 0
  · simp [incrementsCompletionPositiveSlots,hk]
  · rw [incrementsCompletionPositiveSlots_of_pos P k (by omega)]
    exact hP k (by omega)

private theorem incrementsCompletion_positive_prefix_bound
    (P : ℕ → ℝ) (hP : ∀ k, 1 ≤ k → 0 ≤ P k)
    {k j : ℕ} (hk : 1 ≤ k) (hkj : k ≤ j) :
    P k ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots P) j := by
  have h := Finset.single_le_sum
    (fun l (_ : l ∈ Finset.range (j+1)) => incrementsCompletionPositiveSlots_nonneg P hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  rw [incrementsCompletionPositiveSlots_of_pos P k hk] at h
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

/-- Only slots 1 through j of both profiles occur in this explicit cost. -/
def incrementsCompletionPositiveCompositionProfile (outer inner : ℕ → ℝ) (j : ℕ) : ℝ :=
  repairEntranceCompositionProfile (incrementsCompletionPositiveSlots outer)
    (incrementsCompletionPositiveSlots inner) j

theorem incrementsCompletionPositiveCompositionProfile_nonneg
    (outer inner : ℕ → ℝ)
    (hOuter : ∀ k, 1 ≤ k → 0 ≤ outer k) (hInner : ∀ k, 1 ≤ k → 0 ≤ inner k)
    (j : ℕ) : 0 ≤ incrementsCompletionPositiveCompositionProfile outer inner j :=
  repairEntranceCompositionProfile_nonneg _ _
    (incrementsCompletionPositiveSlots_nonneg outer hOuter)
    (incrementsCompletionPositiveSlots_nonneg inner hInner) j

theorem incrementsCompletionPositiveSlots_prefix_congr
    (P P' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ j → P k = P' k) :
    bufferedTransitionPrefix (incrementsCompletionPositiveSlots P) j =
      bufferedTransitionPrefix (incrementsCompletionPositiveSlots P') j := by
  unfold bufferedTransitionPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [incrementsCompletionPositiveSlots,hk0]
  · have hkj : k ≤ j := by simpa using hk
    rw [incrementsCompletionPositiveSlots_of_pos P k (by omega),
      incrementsCompletionPositiveSlots_of_pos P' k (by omega),h k (by omega) hkj]

/-- Changing either zero slot, or either tail above j, has no effect. -/
theorem incrementsCompletionPositiveCompositionProfile_prefix_congr
    (outer inner outer' inner' : ℕ → ℝ) (j : ℕ)
    (hOuter : ∀ k, 1 ≤ k → k ≤ j → outer k = outer' k)
    (hInner : ∀ k, 1 ≤ k → k ≤ j → inner k = inner' k) :
    incrementsCompletionPositiveCompositionProfile outer inner j =
      incrementsCompletionPositiveCompositionProfile outer' inner' j := by
  unfold incrementsCompletionPositiveCompositionProfile repairEntranceCompositionProfile
    actualFastChartTransferCost
  rw [incrementsCompletionPositiveSlots_prefix_congr outer outer' j hOuter,
    incrementsCompletionPositiveSlots_prefix_congr inner inner' j hInner]

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The same actual composition, with the slow weight and no value bounds. -/
theorem incrementsCompletion_positive_composition_at
    (outer inner : ℕ → ℝ)
    (hOuter : ∀ k, 1 ≤ k → 0 ≤ outer k) (hInner : ∀ k, 1 ≤ k → 0 ≤ inner k)
    (j : ℕ) (hj : 1 ≤ j)
    (phi : X → Y) (f : Y → Z) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V)
    (hphi : ContDiffOn ℝ ∞ phi U) (hf : ContDiffOn ℝ ∞ f V)
    (hmap : MapsTo phi U V) (x : X) (hx : x ∈ U)
    (ell : ℝ) (hell : 0 < ell)
    (hfjet : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k f (phi x)‖ ≤ outer k)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k phi x‖ ≤ inner k) :
    ell^(j-1)*‖iteratedFDeriv ℝ j (f ∘ phi) x‖ ≤
      incrementsCompletionPositiveCompositionProfile outer inner j := by
  have h := actual_positive_joint_chart_composition
    (incrementsCompletionPositiveSlots inner)
    (incrementsCompletionPositiveSlots_nonneg inner hInner) j hj phi f U V hU hV hphi hf hmap
    x hx ell (bufferedTransitionPrefix (incrementsCompletionPositiveSlots outer) j) hell
    (zero_le_one.trans (one_le_bufferedTransitionPrefix
      (incrementsCompletionPositiveSlots_nonneg outer hOuter) j)) (by
      intro k hk hkj
      exact (hfjet k hk hkj).trans (incrementsCompletion_positive_prefix_bound outer hOuter hk hkj)) (by
      intro k hk hkj
      rw [incrementsCompletionPositiveSlots_of_pos inner k hk]
      exact hphijet k hk hkj)
  exact h

/-- The actual partial-homeomorphism composition on its unchanged source. -/
theorem incrementsCompletion_positive_trans_chart_at
    (FF GF : ℕ → ℝ)
    (hFF : ∀ k, 1 ≤ k → 0 ≤ FF k) (hGF : ∀ k, 1 ≤ k → 0 ≤ GF k)
    (f : OpenPartialHomeomorph X Y) (g : OpenPartialHomeomorph Y Z)
    (hf : ContDiffOn ℝ ∞ f f.source) (hg : ContDiffOn ℝ ∞ g g.source)
    (j : ℕ) (hj : 1 ≤ j) (x : X) (hx : x ∈ (f.trans g).source)
    (hfJ : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k f x‖ ≤ FF k)
    (hgJ : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k g (f x)‖ ≤ GF k) :
    ‖iteratedFDeriv ℝ j (f.trans g) x‖ ≤
      incrementsCompletionPositiveCompositionProfile GF FF j := by
  have h := incrementsCompletion_positive_composition_at GF FF hGF hFF j hj f g
    (f.trans g).source g.source (f.trans g).open_source g.open_source
    (hf.mono (fun _ hy => hy.1)) hg (fun _ hy => hy.2) x hx 1 zero_lt_one
    (by intro k hk hkj; simpa only [one_pow,one_mul] using hgJ k hk hkj)
    (by intro k hk hkj; simpa only [one_pow,one_mul] using hfJ k hk hkj)
  change ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ incrementsCompletionPositiveCompositionProfile GF FF j
  simpa only [one_pow,one_mul] using h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletionPositiveCompositionProfile_prefix_congr
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_composition_at
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_trans_chart_at
