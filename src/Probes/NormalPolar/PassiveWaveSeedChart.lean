import NormalPolar.PassiveParameterChart
import NormalPolar.ParameterDisplacementPrescribedRaw

/-! Smoothness of the literal passive extension of an actual adapted seed
chart. The original source and target are pulled back through the projection;
the new parameter coordinate is retained as an actual coordinate. -/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M S Ep D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem passiveWaveSeed_chart_smooth (s₀ : S)
    (a : OpenPartialHomeomorph (S × M) (S × D))
    (ha : ContMDiffOn ((𝓘(ℝ,S)).prod I) 𝓘(ℝ,S × D) ∞ a a.source) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,Ep × D) ∞
      (passiveParameterChart s₀ a) (passiveParameterChart (P := Ep) s₀ a).source := by
  let κ : Ep × M → S × M := fun z => (s₀,z.2)
  have hκ : ContMDiff ((𝓘(ℝ,Ep)).prod I) ((𝓘(ℝ,S)).prod I) ∞ κ :=
    contMDiff_const.prodMk contMDiff_snd
  have hcomp := ha.comp hκ.contMDiffOn (fun _ h => h)
  exact contMDiffOn_fst.prodMk_space
    (contDiff_snd.contMDiff.comp_contMDiffOn hcomp)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_chart_smooth
