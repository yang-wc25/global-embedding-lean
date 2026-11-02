import NormalPolar.PassiveWaveSeedChart

/-! The actual parameter-chart conjugate of a passive source chart. Its
domain is the real parameter target, not an artificial unrestricted chart.
The native spatial map is equal to the passive one throughout that domain. -/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {S P M Ep D : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]
  [TopologicalSpace M] [TopologicalSpace Ep] [TopologicalSpace D]

theorem passiveWaveSeed_native_source (s₀ : S)
    (B : OpenPartialHomeomorph P Ep)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : Ep × M) :
    z ∈ (round3ParameterChartPullback B (passiveParameterChart s₀ a)).source ↔
      z.1 ∈ B.target ∧ (s₀,z.2) ∈ a.source := by
  rw [round3ParameterChartPullback_source]
  constructor
  · exact fun hz => ⟨hz.1,hz.2.1⟩
  · intro hz
    exact ⟨hz.1,hz.2,B.map_target hz.1⟩

theorem passiveWaveSeed_native_target (s₀ : S)
    (B : OpenPartialHomeomorph P Ep)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : Ep × D) :
    z ∈ (round3ParameterChartPullback B (passiveParameterChart s₀ a)).target ↔
      z.1 ∈ B.target ∧ (s₀,z.2) ∈ a.target := by
  rw [round3ParameterChartPullback_target]
  constructor
  · exact fun hz => ⟨hz.1,hz.2.1⟩
  · intro hz
    exact ⟨hz.1,hz.2,B.map_target hz.1⟩

theorem passiveWaveSeed_native_apply (s₀ : S)
    (B : OpenPartialHomeomorph P Ep)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : Ep × M)
    (hz : z.1 ∈ B.target) :
    round3ParameterChartPullback B (passiveParameterChart s₀ a) z =
      passiveParameterChart s₀ a z := by
  change (B (B.symm z.1),(a (s₀,z.2)).2) = (z.1,(a (s₀,z.2)).2)
  rw [B.right_inv hz]

theorem passiveWaveSeed_native_symm (s₀ : S)
    (B : OpenPartialHomeomorph P Ep)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (z : Ep × D)
    (hz : z.1 ∈ B.target) :
    (round3ParameterChartPullback B (passiveParameterChart s₀ a)).symm z =
      (passiveParameterChart s₀ a).symm z := by
  change (B (B.symm z.1),(a.symm (s₀,z.2)).2) = (z.1,(a.symm (s₀,z.2)).2)
  rw [B.right_inv hz]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_native_source
#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_native_apply
