import NormalPolar.PassiveParameterChart

/-! A nonempty chart on the actual zero-dimensional singleton parameter
space is the identity chart, including its entire source and global maps.
This discharges the identity-chart requirement of the genuine seed factory;
no original parameter chart is replaced. -/

noncomputable section
open Set
namespace GlobalEmbedding.Continuation

theorem passiveParameter_subsingleton_chart_eq_refl
    {S : Type*} [TopologicalSpace S] [Subsingleton S]
    (B : OpenPartialHomeomorph S S) (s₀ : S) (hs₀ : s₀ ∈ B.source) :
    B = OpenPartialHomeomorph.refl S := by
  apply OpenPartialHomeomorph.ext
  · intro s; exact Subsingleton.elim _ _
  · intro s; exact Subsingleton.elim _ _
  · ext s
    constructor
    · intro _; exact mem_univ _
    · intro _
      exact (Subsingleton.elim s₀ s) ▸ hs₀

theorem passiveParameter_pullback_refl
    {P M D : Type*} [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace D]
    (a : OpenPartialHomeomorph (P × M) (P × D)) :
    round3ParameterChartPullback (OpenPartialHomeomorph.refl P) a = a := by
  apply OpenPartialHomeomorph.ext
  · intro z; rfl
  · intro z; rfl
  · ext z
    rw [round3ParameterChartPullback_source]
    change (z.1 ∈ (univ : Set P) ∧ z ∈ a.source ∧ (a z).1 ∈ (univ : Set P)) ↔ z ∈ a.source
    simp only [mem_univ,true_and,and_true]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveParameter_subsingleton_chart_eq_refl
#print axioms GlobalEmbedding.Continuation.passiveParameter_pullback_refl
