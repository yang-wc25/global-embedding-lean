import Probes.Round3ParameterNativeFamily

/-! Exact parameter-chart conjugation for a physical spatial product chart.
The actual B target is retained on both sides. Function equalities are used
only there, with no assertion about the arbitrary extension off the chart. -/

noncomputable section
open Set
namespace GlobalEmbedding.Continuation

variable {P Ep M D : Type*} [TopologicalSpace P] [TopologicalSpace Ep]
  [TopologicalSpace M] [TopologicalSpace D]

theorem passiveSecondarySeed_chart_source (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (z : Ep × M) :
    z ∈ (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).source ↔
      z.1 ∈ B.target ∧ z.2 ∈ e.source := by
  rw [round3ParameterChartPullback_source]
  constructor
  · intro hz
    exact ⟨hz.1,hz.2.1.2⟩
  · intro hz
    exact ⟨hz.1,⟨mem_univ _,hz.2⟩,B.map_target hz.1⟩

theorem passiveSecondarySeed_chart_target (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (z : Ep × D) :
    z ∈ (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).target ↔
      z.1 ∈ B.target ∧ z.2 ∈ e.target := by
  rw [round3ParameterChartPullback_target]
  constructor
  · intro hz
    exact ⟨hz.1,hz.2.1.2⟩
  · intro hz
    exact ⟨hz.1,⟨mem_univ _,hz.2⟩,B.map_target hz.1⟩

theorem passiveSecondarySeed_chart_apply (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (z : Ep × M) (hz : z.1 ∈ B.target) :
    round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e) z =
      (z.1,e z.2) := by
  change (B (B.symm z.1),e z.2) = _
  rw [B.right_inv hz]

theorem passiveSecondarySeed_chart_symm (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (z : Ep × D) (hz : z.1 ∈ B.target) :
    (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).symm z =
      (z.1,e.symm z.2) := by
  change (B (B.symm z.1),e.symm z.2) = _
  rw [B.right_inv hz]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_chart_source
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_chart_target
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_chart_apply
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_chart_symm
