import Smoothing.ParameterRound2OriginalGermArgumentSmooth
import Probes.ActualIncrementOriginalSampleCoverage

/-! Return actual original coordinate germs to the same physical map.
This is used by the constructed normal, including its open primary-domain
regularity.  Closed parameter evaluation supplies a true physical cover from
the original samples; full chart targets are never assumed to be norm sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)

theorem round3_repair_original_map_contMDiffAt_of_coordinate_germ
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (f : P × M → Ey) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (O : Set (Fin (n+d) → ℝ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f i) O)
    (z : P × M) (hp : z.1 ∈ (Data.parameterChart i.2).source)
    (hx : z.2 ∈ (Data.atlas.chart i.1).source)
    (hz : parameterRound2_originalForwardCoordinates Data i z ∈ O) :
    ContMDiffAt ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ f z := by
  let phi := parameterRound2_originalForwardCoordinates Data i
  have hphi : ContMDiffAt ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Fin (n+d) → ℝ) ∞ phi z :=
    (parameterTensorModelEquiv n d).contDiff.comp_contMDiffAt
      ((((contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).contMDiffAt
        ((Data.parameterChart i.2).open_source.mem_nhds hp)).comp z contMDiffAt_fst).prodMk_space
        (((contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).contMDiffAt
          ((Data.atlas.chart i.1).open_source.mem_nhds hx)).comp z contMDiffAt_snd))
  have hcoords := (hf.contDiffAt (hO.mem_nhds hz)).comp_contMDiffAt hphi
  have hreg := (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contMDiffAt hcoords
  apply hreg.congr_of_eventuallyEq
  filter_upwards [((Data.parameterChart i.2).open_source.preimage continuous_fst).mem_nhds hp,
    ((Data.atlas.chart i.1).open_source.preimage continuous_snd).mem_nhds hx] with w hwp hwx
  have he := parameterRound2_originalForward_left_inv Data i w hwp hwx
  change f w = (EuclideanSpace.equiv (Fin N) ℝ).symm
    ((EuclideanSpace.equiv (Fin N) ℝ) (f (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi w))))
  rw [(EuclideanSpace.equiv (Fin N) ℝ).symm_apply_apply,he]

/-- A physical point above K belongs to a literal original sample in a
chart whose actual forward map is used.  This also gives a source-open
neighborhood for applying coordinate germs at that point. -/
theorem round3_repair_original_forward_sample
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (z : P × M) (hz : z.1 ∈ Data.parameterSet) :
    ∃ i : Fin Data.atlas.count × Fin Data.parameterCount,
      z.1 ∈ (Data.parameterChart i.2).source ∧ z.2 ∈ (Data.atlas.chart i.1).source ∧
      parameterRound2_originalForwardCoordinates Data i z ∈ incrementsOriginalEvaluation
        Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i := by
  obtain ⟨a,ha⟩ := Data.atlas.cover z.2
  obtain ⟨b,hb,hbn⟩ := hd.parameter_cover z.1 hz
  let i : Fin Data.atlas.count × Fin Data.parameterCount := (a,b)
  have hx : z.2 ∈ (Data.atlas.chart i.1).source := Data.atlas.inner_subset a ha
  have he := parameterRound2_originalForward_left_inv Data i z hb hx
  have hm := parameterRound2_originalForward_mem Data i z hb hx
  have hc := parameterRound2_originalForward_components Data i z
  refine ⟨i,hb,hx,hm,?_,?_,?_⟩
  · change incrementsOriginalSourcePoint (parameterRound2_originalForwardCoordinates Data i z) ∈ Data.sourceNormDomain i.1
    have hx' : incrementsOriginalSourcePoint (parameterRound2_originalForwardCoordinates Data i z) =
        Data.atlas.chart i.1 z.2 := congrArg Prod.snd hc
    rw [hx']
    exact hd.source_inner_norm a z.2 ha
  · change incrementsOriginalParameterPoint (parameterRound2_originalForwardCoordinates Data i z) ∈ Data.parameterNormDomain i.2
    have hp' : incrementsOriginalParameterPoint (parameterRound2_originalForwardCoordinates Data i z) =
        Data.parameterChart i.2 z.1 := congrArg Prod.fst hc
    rw [hp']
    exact hbn
  · change (incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterRound2_originalForwardCoordinates Data i z)).1 ∈ Data.parameterSet
    rw [he]
    exact hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_original_map_contMDiffAt_of_coordinate_germ
#print axioms GlobalEmbedding.Continuation.round3_repair_original_forward_sample
