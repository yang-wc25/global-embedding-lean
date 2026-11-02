import Probes.Round3ParameterPrimaryChartSmooth

/-! Both sides of the exact nonlinear parameter conjugation are smooth.
The resulting observer-to-primary maps are actual maps on Ep×D, so their
iterated derivatives are total parameter/spatial derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3ParameterChartPullback_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a a.source)
    (hai : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞
      (round3ParameterChartPullback B a) (round3ParameterChartPullback B a).source ∧
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3ParameterChartPullback B a).symm (round3ParameterChartPullback B a).target := by
  let qM := round3ParameterProductChart (M := M) B
  let qD := round3ParameterProductChart (M := D) B
  have hM := round3ParameterProductChart_smooth (n := m+1) (M := M) B hB
  have hMi := round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B hB
  have hD : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ qD qD.source :=
    ((contMDiffOn_of_mem_maximalAtlas hB).comp contMDiffOn_fst (fun _ hz => hz.1)).prodMk_space contMDiffOn_snd
  have hDi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ qD.symm qD.target :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hB).comp
      contDiff_fst.contMDiff.contMDiffOn (fun _ hz => hz.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  exact ⟨round3Parameter_partial_trans_smooth (qM.symm.trans a) qD
      (round3Parameter_partial_trans_smooth qM.symm a hMi ha) hD,
    round3Parameter_partial_trans_symm_smooth (qM.symm.trans a) qD
      (round3Parameter_partial_trans_symm_smooth qM.symm a hM hai) hDi⟩

theorem round3Parameter_native_observer_transition_smooth
    (a : OpenPartialHomeomorph (Ep × M) X)
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ a a.source)
    (hai : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M) :
    let t := ((OpenPartialHomeomorph.refl Ep).prod e).symm.trans a
    ContDiffOn ℝ ∞ t t.source ∧ ContDiffOn ℝ ∞ t.symm t.target := by
  intro t
  let b := (OpenPartialHomeomorph.refl Ep).prod e
  have hb : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ b b.source :=
    contMDiffOn_fst.prodMk_space ((contMDiffOn_of_mem_maximalAtlas he).comp contMDiffOn_snd (fun _ hz => hz.2))
  have hbi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm b.target :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk ((contMDiffOn_symm_of_mem_maximalAtlas he).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have ht := round3Parameter_partial_trans_smooth b.symm a hbi ha
  have hti := round3Parameter_partial_trans_symm_smooth b.symm a hb hai
  exact ⟨ht.contDiffOn,hti.contDiffOn⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterChartPullback_smooth
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_observer_transition_smooth
