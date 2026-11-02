import Probes.ActualBoundedRefinementCover

/-!
# A fixed-radius refinement has a uniformly bounded total number of pieces

The bound is selected from a cover of the one universal model ball before
any actual piece, phase, center, map, small iteration scale or observation
order. This is distinct from the local multiplicity bound for a varying
slow-scale refinement.
-/

noncomputable section
open Set Function Metric
open scoped NNReal
namespace GlobalEmbedding.Continuation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem actual_exists_uniform_total_refinement_bound (R r : ℝ) (hr : 0 < r) :
    ∃ L : ℕ, ∀ (s : Finset E) (c : E),
      (∀ a ∈ s, dist a c ≤ R) →
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) → s.card ≤ L := by
  classical
  let d : ℝ≥0 := ⟨r/4,by positivity⟩
  have hd : d ≠ 0 := by
    intro hz
    have hh : r/4 = 0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) hz
    linarith
  obtain ⟨N,_,hNfin,hNc⟩ := exists_finite_isCover_of_isCompact hd
    (isCompact_closedBall (0 : E) R)
  let : Fintype N := hNfin.fintype
  refine ⟨Fintype.card N,?_⟩
  intro s c hball hsep
  have hcover : ∀ a : s, ∃ b : N, dist (a.val-c) b.val ≤ r/4 := by
    intro a
    have ha : a.val-c ∈ closedBall (0 : E) R := by
      simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hball a.val a.property
    obtain ⟨b,hb,hba⟩ := hNc ha
    exact ⟨⟨b,hb⟩,edist_le_coe.mp hba⟩
  choose f hf using hcover
  have hinj : Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have ha := hf a
    have hb := hf b
    rw [hab] at ha
    have hdis : dist (a.val-c) (b.val-c) ≤ r/2 := by
      calc
        _ ≤ dist (a.val-c) (f b).val + dist (f b).val (b.val-c) := dist_triangle _ _ _
        _ ≤ r/4+r/4 := add_le_add ha (by simpa only [dist_comm] using hb)
        _ = r/2 := by ring
    have hlower := hsep a.val a.property b.val b.property hne
    rw [dist_sub_right] at hdis
    linarith
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_total_refinement_bound
