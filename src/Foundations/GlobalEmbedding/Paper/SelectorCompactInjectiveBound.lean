import GlobalEmbedding.Paper.FreeCorrectionStability

/-!
# A uniform original-norm bound for a compact injective operator field

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 584–587.
DAG: `selector-compact-injective-bound`. Exclusive proof owner W5.
-/

noncomputable section
namespace GlobalEmbedding.Paper

/-- A continuous field of injective operators on a compact source has one positive
homogeneous lower bound in the original norms, including empty sources and zero-dimensional E.

Proof: if E is subsingleton, every vector is zero, so the constant 1 works. Otherwise apply
`free_compact_injective_lower_bound` directly to the compact set `univ` and the same field A.
That accepted theorem already includes empty compact patches. No norm, operator family,
pointwise injectivity hypothesis or compact-minimum proof is replaced. -/
theorem selector_compact_injective_bound {X E F : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : X → E →L[ℝ] F) (hA : Continuous A)
    (hinj : ∀ x, Function.Injective (A x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x v, ε * ‖v‖ ≤ ‖A x v‖ := by
  rcases subsingleton_or_nontrivial E with hzero | hnonzero
  · have : Subsingleton E := hzero
    refine ⟨1, zero_lt_one, ?_⟩
    intro x v
    simp [Subsingleton.elim v 0]
  · have : Nontrivial E := hnonzero
    obtain ⟨ε, hε, hbound⟩ := free_compact_injective_lower_bound
      (K := Set.univ) isCompact_univ A hA.continuousOn (fun x _ ↦ hinj x)
    exact ⟨ε, hε, fun x v ↦ hbound x (Set.mem_univ x) v⟩

#print axioms selector_compact_injective_bound

end GlobalEmbedding.Paper
