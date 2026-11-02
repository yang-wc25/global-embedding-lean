import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Actual compact-pair protection for the embedding upgrade

The protected set is recomputed from the **current** map.  No fixed list of old
zeros, support of the corrected map, connectedness, orientation, or nonempty
source is assumed.  The neighborhood has a protected closure and the estimate
retains both endpoint errors.  Source: the paragraphs following (10.1), and the
three-dimensional supported-coincidence paragraph of `thm:upgrade`.
-/

open Set Topology

namespace GlobalEmbedding.Upgrade

section CompactMinimum

variable {X : Type*} [TopologicalSpace X]

/-- A continuous positive function has a uniform positive lower bound on a
compact set, including the empty-set case. -/
theorem compact_positive_lower_bound {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ d > 0, ∀ x ∈ K, d < f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, by norm_num, by simp [h]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn h hf
    refine ⟨f x / 2, half_pos (hpos x hx), ?_⟩
    intro y hy
    exact (half_lt_self (hpos x hx)).trans_le (hmin hy)

end CompactMinimum

section PairProtection

variable {M E : Type*} [TopologicalSpace M] [T2Space M] [RegularSpace M]
  [NormedAddCommGroup E]

/-- Construct an actual protected source neighborhood.  All pairs in `P`
meeting its closure have one common positive value gap.  The hypothesis is
separation only on the **current** compact bad set `S`. -/
theorem exists_protected_pair_neighborhood
    {P : Set (M × M)} (hP : IsCompact P) {S : Set M} (hS : IsCompact S)
    {F : M → E} (hF : Continuous F)
    (hsep : ∀ z ∈ P, z.1 ∈ S ∨ z.2 ∈ S → F z.1 ≠ F z.2) :
    ∃ O : Set M, IsOpen O ∧ S ⊆ O ∧
      ∃ d > 0, ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
        d < ‖F z.1 - F z.2‖ := by
  let D : M × M → ℝ := fun z ↦ ‖F z.1 - F z.2‖
  have hD : Continuous D := (hF.comp continuous_fst |>.sub
    (hF.comp continuous_snd)).norm
  let K : Set (M × M) := P ∩ (Prod.fst ⁻¹' S ∪ Prod.snd ⁻¹' S)
  have hK : IsCompact K := hP.inter_right
    ((hS.isClosed.preimage continuous_fst).union
      (hS.isClosed.preimage continuous_snd))
  obtain ⟨d, hd, hgap⟩ := compact_positive_lower_bound hK hD.continuousOn
    (fun z hz ↦ norm_pos_iff.mpr (sub_ne_zero.mpr (hsep z hz.1 hz.2)))
  let Q : Set (M × M) := P ∩ {z | D z ≤ d}
  have hQ : IsCompact Q := hP.inter_right (isClosed_le hD continuous_const)
  let T : Set M := Prod.fst '' Q ∪ Prod.snd '' Q
  have hT : IsClosed T := ((hQ.image continuous_fst).union
    (hQ.image continuous_snd)).isClosed
  have hST : S ⊆ Tᶜ := by
    intro x hx hxt
    rcases hxt with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact (not_lt_of_ge hz.2) (hgap z ⟨hz.1, Or.inl hx⟩)
    · exact (not_lt_of_ge hz.2) (hgap z ⟨hz.1, Or.inr hx⟩)
  obtain ⟨O, hO, hSO, hOT⟩ := hS.exists_isOpen_closure_subset
    (hT.isOpen_compl.mem_nhdsSet.mpr hST)
  refine ⟨O, hO, hSO, d, hd, ?_⟩
  intro z hz hzo
  by_contra h
  have hzQ : z ∈ Q := ⟨hz, le_of_not_gt h⟩
  rcases hzo with hx | hy
  · exact hOT hx (Or.inl ⟨z, hzQ, rfl⟩)
  · exact hOT hy (Or.inr ⟨z, hzQ, rfl⟩)

omit [TopologicalSpace M] [T2Space M] [RegularSpace M] in
/-- Both global endpoint errors enter the protection estimate.  In particular
the correction need not vanish away from a selected local wave. -/
theorem pair_gap_lower_after_perturbation
    (F G : M → E) (x y : M) (d e : ℝ)
    (hgap : d ≤ ‖F x - F y‖)
    (hx : ‖G x - F x‖ ≤ e) (hy : ‖G y - F y‖ ≤ e) :
    d - 2 * e ≤ ‖G x - G y‖ := by
  have hsub : (F x - F y) - (G x - G y) =
      -(G x - F x) + (G y - F y) := by abel
  have hnorm := norm_sub_norm_le (F x - F y) (G x - G y)
  rw [hsub] at hnorm
  have htri := norm_add_le (-(G x - F x)) (G y - F y)
  rw [norm_neg] at htri
  linarith

omit [T2Space M] [RegularSpace M] in
/-- A quarter-gap perturbation preserves half of every protected pair gap. -/
theorem protected_pair_gap_after_perturbation
    (F G : M → E) {O : Set M} {P : Set (M × M)} {d : ℝ}
    (hgap : ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
      d < ‖F z.1 - F z.2‖)
    (hclose : ∀ x, ‖G x - F x‖ ≤ d / 4) :
    ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
      d / 2 ≤ ‖G z.1 - G z.2‖ := by
  intro z hz hzo
  have h := pair_gap_lower_after_perturbation F G z.1 z.2 d (d / 4)
    (hgap z hz hzo).le (hclose z.1) (hclose z.2)
  linarith

omit [T2Space M] [RegularSpace M] in
/-- After protecting a neighborhood, every new distant coincidence is in its
compact complement at **both** endpoints. -/
theorem coincidence_mem_complement_prod_of_protected_gap
    {G : M → E} {O : Set M} {P : Set (M × M)} {d : ℝ} (hd : 0 < d)
    (hgap : ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
      d ≤ ‖G z.1 - G z.2‖) :
    ∀ z ∈ P, G z.1 = G z.2 → z ∈ Oᶜ ×ˢ Oᶜ := by
  intro z hz heq
  have hnot : ¬(z.1 ∈ closure O ∨ z.2 ∈ closure O) := by
    intro h
    have hle := hgap z hz h
    rw [heq, sub_self, norm_zero] at hle
    exact (not_le_of_gt hd) hle
  exact ⟨fun hx ↦ hnot (Or.inl (subset_closure hx)),
    fun hy ↦ hnot (Or.inr (subset_closure hy))⟩

end PairProtection

end GlobalEmbedding.Upgrade
