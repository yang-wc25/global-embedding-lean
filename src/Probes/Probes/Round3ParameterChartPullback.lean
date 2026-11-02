import Probes.Round3ParameterPrimaryConstruction

/-! Genuine parameter-chart conjugation.  The nonlinear parameter chart is
retained on both sides; only spatial derivatives will later be compared. -/

noncomputable section
open Set
namespace GlobalEmbedding.Continuation

variable {P Q M D : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [TopologicalSpace D]

def round3ParameterChartPullback (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D)) :
    OpenPartialHomeomorph (Q × M) (Q × D) :=
  ((B.prod (OpenPartialHomeomorph.refl M)).symm.trans a).trans
    (B.prod (OpenPartialHomeomorph.refl D))

theorem round3ParameterChartPullback_source (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (z : Q × M) :
    z ∈ (round3ParameterChartPullback B a).source ↔
      z.1 ∈ B.target ∧ (B.symm z.1,z.2) ∈ a.source ∧
        (a (B.symm z.1,z.2)).1 ∈ B.source := by
  simp [round3ParameterChartPullback, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source, and_assoc]

theorem round3ParameterChartPullback_target (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (z : Q × D) :
    z ∈ (round3ParameterChartPullback B a).target ↔
      z.1 ∈ B.target ∧ (B.symm z.1,z.2) ∈ a.target ∧
        (a.symm (B.symm z.1,z.2)).1 ∈ B.source := by
  simp [round3ParameterChartPullback, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.prod_target, and_assoc]

theorem round3ParameterChartPullback_apply (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (z : Q × M) :
    round3ParameterChartPullback B a z =
      (B (a (B.symm z.1,z.2)).1, (a (B.symm z.1,z.2)).2) := rfl

theorem round3ParameterChartPullback_symm_apply (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D)) (z : Q × D) :
    (round3ParameterChartPullback B a).symm z =
      (B (a.symm (B.symm z.1,z.2)).1, (a.symm (B.symm z.1,z.2)).2) := rfl

/-- The actual spatial chart does not change the physical parameter. -/
def Round3ParameterChartPreserves (a : OpenPartialHomeomorph (P × M) (P × D)) : Prop :=
  ∀ z ∈ a.source, (a z).1 = z.1

theorem round3ParameterChartPreserves_inverse
    (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) (z : P × D) (hz : z ∈ a.target) :
    (a.symm z).1 = z.1 := by
  have h := ha (a.symm z) (a.map_target hz)
  rw [a.right_inv hz] at h
  exact h.symm

theorem round3ParameterChartPullback_source_iff (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) (z : Q × M) (hz : z.1 ∈ B.target) :
    z ∈ (round3ParameterChartPullback B a).source ↔
      (B.symm z.1,z.2) ∈ a.source := by
  rw [round3ParameterChartPullback_source]
  constructor
  · exact fun h => h.2.1
  · intro hs
    exact ⟨hz, hs, by rw [ha _ hs]; exact B.map_target hz⟩

theorem round3ParameterChartPullback_target_iff (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) (z : Q × D) (hz : z.1 ∈ B.target) :
    z ∈ (round3ParameterChartPullback B a).target ↔
      (B.symm z.1,z.2) ∈ a.target := by
  rw [round3ParameterChartPullback_target]
  constructor
  · exact fun h => h.2.1
  · intro hs
    exact ⟨hz, hs, by rw [round3ParameterChartPreserves_inverse a ha _ hs]; exact B.map_target hz⟩

theorem round3ParameterChartPullback_preserves (B : OpenPartialHomeomorph P Q)
    (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) :
    Round3ParameterChartPreserves (round3ParameterChartPullback B a) := by
  intro z hz
  obtain ⟨hzB, hza, _⟩ := (round3ParameterChartPullback_source B a z).mp hz
  rw [round3ParameterChartPullback_apply, ha _ hza]
  exact B.right_inv hzB

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterChartPullback_target_iff
#print axioms GlobalEmbedding.Continuation.round3ParameterChartPullback_preserves
