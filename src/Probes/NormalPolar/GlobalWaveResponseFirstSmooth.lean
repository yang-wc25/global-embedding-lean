import NormalPolar.GlobalWaveResponsePrimitiveCharts
import NormalPolar.GlobalWaveResponseSecondaryNorms

/-!
The same original atlas turns actual component chart jointness into global
jointness of the complete first map. No extension in the parameter variable
and no independent whole-map smoothness assumption are used. The reference
may be any smooth map independent of the probe parameter.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {m N : ℕ} {P M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem globalWave_joint_of_original_atlas
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x∈A.support i)
    (U : Set P) (hU : IsOpen U) (G : P→M→V)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (fun z : P×D => G z.1 ((A.chart i).symm z.2))
      (U×ˢ(A.chart i).target)) :
    ContMDiffOn ((𝓘(ℝ,P)).prod IM) 𝓘(ℝ,V) ∞ (Function.uncurry G) (U×ˢuniv) := by
  intro z hz
  obtain ⟨i,hx⟩ := hcover z.2
  have hs := hA.support_subset i hx
  have hc : ContMDiffAt IM 𝓘(ℝ,D) ∞ (A.chart i) z.2 :=
    (contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i)).contMDiffAt
      ((A.chart i).open_source.mem_nhds hs)
  have hPull : ContMDiffAt ((𝓘(ℝ,P)).prod IM) 𝓘(ℝ,P×D) ∞
      (fun w : P×M => (w.1,A.chart i w.2)) z :=
    contMDiffAt_fst.prodMk_space (hc.comp z contMDiffAt_snd)
  have ho : ContDiffAt ℝ ∞ (fun w : P×D => G w.1 ((A.chart i).symm w.2))
      (z.1,A.chart i z.2) := (hJ i).contDiffAt
        ((hU.prod (A.chart i).open_target).mem_nhds ⟨hz.1,(A.chart i).map_source hs⟩)
  have hh := ho.contMDiffAt.comp z hPull
  apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    ((A.chart i).open_source.mem_nhds hs)] with w hw
  exact congrArg (G w.1) ((A.chart i).left_inv hw).symm

theorem globalWave_complete_first_smooth_of_components
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x∈A.support i)
    (U : Set P) (hU : IsOpen U) (reference : M→V)
    (href : ContMDiff IM 𝓘(ℝ,V) ∞ reference)
    (B Pr S : P→M→V)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z : P×D => B z.1 ((A.chart i).symm z.2))
      (U×ˢ(A.chart i).target))
    (hP : ∀ i, ContDiffOn ℝ ∞ (fun z : P×D => Pr z.1 ((A.chart i).symm z.2))
      (U×ˢ(A.chart i).target))
    (hS : ∀ i, ContDiffOn ℝ ∞ (fun z : P×D => S z.1 ((A.chart i).symm z.2))
      (U×ˢ(A.chart i).target)) :
    let G := fun u x => reference x+B u x+Pr u x+S u x
    ContMDiffOn ((𝓘(ℝ,P)).prod IM) 𝓘(ℝ,V) ∞ (Function.uncurry G) (U×ˢuniv) ∧
    ∀ u∈U, ContMDiff IM 𝓘(ℝ,V) ∞ (G u) := by
  intro G
  have hRef (i : Fin A.count) : ContDiffOn ℝ ∞
      (fun z : P×D => reference ((A.chart i).symm z.2)) (U×ˢ(A.chart i).target) :=
    ((href.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn).comp
      (ContinuousLinearMap.snd ℝ P D).contDiff.contDiffOn (fun z hz => hz.2)
  have hJoint := globalWave_joint_of_original_atlas A hA hcover U hU G
    (fun i => (((hRef i).add (hB i)).add (hP i)).add (hS i))
  refine ⟨hJoint,?_⟩
  intro u hu
  apply contMDiffOn_univ.1
  exact hJoint.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun x _ => ⟨hu,mem_univ x⟩)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_joint_of_original_atlas
#print axioms GlobalEmbedding.NormalPolar.globalWave_complete_first_smooth_of_components
