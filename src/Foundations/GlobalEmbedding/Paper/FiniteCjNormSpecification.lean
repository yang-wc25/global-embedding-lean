import GlobalEmbedding.Paper.FiniteCjNorm

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, actual finite derivative supremum norms. -/

namespace GlobalEmbedding.Paper

/-- Under explicit finite derivative suprema, the actual Cj norm is nonnegative,
bounds every derivative through order j, is bounded by the sum of nonnegative
pointwise derivative bounds, and vanishes on the empty domain.

Proof: each supremum set contains zero. Its least-upper-bound characterization
bounds each pointwise value and each summand; sum the nonnegative summands.
For empty U all sets reduce to {0}. Source: `prop:initialization` proof, line822. -/
theorem finiteCjNorm_specification
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (f : D → F) (U : Set D)
    (hf : ∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖)) :
    0 ≤ finiteCjNorm j f U ∧
    (∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k f x‖ ≤ finiteCjNorm j f U) ∧
    (∀ L : ℕ → ℝ, (∀ k ≤ j, 0 ≤ L k) →
      (∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k f x‖ ≤ L k) →
      finiteCjNorm j f U ≤ ∑ k ∈ Finset.range (j + 1), L k) ∧
    (U = ∅ → finiteCjNorm j f U = 0) := by
  have hnonneg : ∀ k ≤ j,
      0 ≤ sSup (insert 0 (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖)) := by
    intro k hk
    exact le_csSup ((hf k hk).insert 0) (Set.mem_insert _ _)
  refine ⟨Finset.sum_nonneg (fun k hk ↦ hnonneg k (by simpa using hk)), ?_, ?_, ?_⟩
  · intro k hk x hx
    have hpoint : ‖iteratedFDeriv ℝ k f x‖ ≤
        sSup (insert 0 (Set.range fun y : U ↦ ‖iteratedFDeriv ℝ k f y‖)) :=
      le_csSup ((hf k hk).insert 0) (Set.mem_insert_of_mem 0 ⟨⟨x, hx⟩, rfl⟩)
    exact hpoint.trans (Finset.single_le_sum
      (fun l hl ↦ hnonneg l (by simpa using hl)) (by simpa using hk))
  · intro L hL hbound
    apply Finset.sum_le_sum
    intro k hk
    have hkj : k ≤ j := by simpa using hk
    apply csSup_le (Set.insert_nonempty _ _)
    rintro r (rfl | ⟨x, rfl⟩)
    · exact hL k hkj
    · exact hbound k hkj x x.property
  · rintro rfl
    simp [finiteCjNorm, Set.range_eq_empty]

end GlobalEmbedding.Paper
