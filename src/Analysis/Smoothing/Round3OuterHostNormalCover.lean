import Smoothing.Round3OuterNormalCoverGeometry
import Smoothing.Round3OuterOriginalChartPoint
import Probes.ActualIncrementHostGeometryInputs
import Probes.ActualIncrementOriginalFamilyKernel
import Probes.ActualIncrementOriginalSampling

/-! Actual host-adapted charts construct the normal cover. Its open domains,
observer maps, sample membership and physical-point equality come from the
original charts and genuine slice data. The lower reserves are precisely
the outputs of the fixed-reference C2 stability construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

def round3HostNormalCover
    {A : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hId : ∀ ip, Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (nu : Fin Data.primaryCount) (domain : Set (Ep × M))
    (host : A → Fin Data.atlas.count) (b : A → OpenPartialHomeomorph X X)
    (e : A → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ a, ActualOriginalHostSliceData (Data.atlas.chart (host a)) (b a) (Data.phase nu) (e a))
    (hActive : ∀ a, (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hInner : ∀ a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source →
      w.2 ∈ Data.atlas.inner (host a))
    (hCover : ∀ w ∈ domain, ∃ a, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source)
    (cF cT mu : ℝ)
    (hFirst : ∀ a z, z ∈ (b a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F (z.1,x)) ∘ (e a z.1).symm) z.2 w‖^2)
    (hFrame : ∀ a z, z ∈ (b a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F (z.1,x)) (hF z.1)
        (e a z.1).symm z.2 w‖^2)
    (hReserve : ∀ a z, z ∈ (b a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F (p,x)) hF (e a)
        (fun z : X => Data.freeNormal nu (z.1,(e a z.1).symm z.2)) z‖) :
    Round3OriginalNormalCoverGeometry Data hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu) A
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (fun i => incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ∩
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹' domain) cF cT mu := by
  let chart := fun a => actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)
  let point := incrementsOriginalJointPoint Data.atlas Data.parameterChart
  let U := fun i a => incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
    point i ⁻¹' (chart a).source
  let forward := fun i a => chart a ∘ point i
  have hU (i) (a : A) : IsOpen (U i a) :=
    (actual_original_jointPoint_continuousOn Data i).isOpen_inter_preimage
      (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i) (chart a).open_source
  have hMap (i) (a : A) : MapsTo (forward i a) (U i a) (b a).target := by
    intro y hy
    rw [← (hData a).1]
    exact (chart a).map_source hy.2
  have hSame (i) (a : A) (y : Y) (hy : y ∈ U i a) :
      ((Data.parameterChart i.2).symm (forward i a y).1,
        (e a (forward i a y).1).symm (forward i a y).2) = point i y := by
    rcases hData a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    rw [hId]
    change ((forward i a y).1,(e a (forward i a y).1).symm (forward i a y).2) = _
    exact (hpair _ (hMap i a hy)).symm.trans ((chart a).left_inv hy.2)
  have hGeometry (a : A) := actual_host_slice_geometry_inputs
    (Data.atlas.chart (host a)) (hd.atlas_smooth.chart_mem (host a)) (b a) (Data.phase nu) (e a) (hData a)
  have hNormal (a : A) : ContDiffOn ℝ ∞
      (fun z : X => Data.freeNormal nu (z.1,(e a z.1).symm z.2)) (b a).target := by
    rcases hData a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    have hh := ((hs.normal_joint nu).comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ (b a).target) => hActive a ((chart a).map_target (by rwa [hat])))).contDiffOn
    apply hh.congr
    intro z hz
    exact congrArg (Data.freeNormal nu) (hpair z hz).symm
  refine {
    host := fun i a => (host a,i.2)
    chart := fun _ a => e a
    native := fun _ a => (b a).target
    original := U
    forward := forward
    original_open := hU
    native_open := fun _ a => (b a).open_target
    original_subset := fun _ _ _ hy => hy.1
    covers := ?_
    chart_smooth := fun _ a => (hData a).2.2.2.2.1
    forward_smooth := ?_
    forward_maps := hMap
    same_point := hSame
    chart_target := fun _ a z hz => ((hGeometry a).2.2.2.1 z hz).1
    source := fun _ a z hz => ((hGeometry a).2.2.2.1 z hz).2
    parameter := ?_
    transition_smooth := fun _ a => (hGeometry a).2.2.2.2.1
    phase_smooth := ?_
    phase_adapted := ?_
    reference_smooth := ?_
    sample := ?_
    first := ?_
    transverse := ?_
    reserve := ?_ }
  · intro i y hy
    obtain ⟨a,ha⟩ := hCover _ hy.2
    exact ⟨a,hy.1.1,ha⟩
  · intro i a
    exact (((hData a).2.1).comp
      ((round3_original_jointPoint_contMDiffOn Data.atlas Data.parameterChart
        hd.atlas_smooth hd.parameter_charts_smooth i).mono inter_subset_left)
      (fun _ hy => hy.2)).contDiffOn
  · intro i a z hz
    rw [hId]
    exact mem_univ _
  · intro i a z hz
    rw [hId]
    have hpoint := actual_host_slice_source_point (Data.atlas.chart (host a)) (b a)
      (Data.phase nu) (e a) (hData a) z hz
    have hact := hActive a hpoint
    have hW := (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
    exact (((hs.phase_joint nu).contMDiffAt (hW.mem_nhds hact)).comp
      ((e a z.1).symm z.2) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  · intro i a z hz
    rw [hId]
    exact (hGeometry a).2.2.2.2.2.2.2 z hz
  · intro i a
    change ContDiffOn ℝ ∞ (fun z : X => Data.freeNormal nu
      ((Data.parameterChart i.2).symm z.1,(e a z.1).symm z.2)) (b a).target
    simpa only [hId i.2,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using hNormal a
  · intro i a y hy
    let z := forward i a y
    have hz : z ∈ (b a).target := hMap i a hy.2
    have hpoint := actual_host_slice_source_point (Data.atlas.chart (host a)) (b a)
      (Data.phase nu) (e a) (hData a) z hz
    have hp : z.1 = incrementsOriginalParameterPoint y := by
      have hh := congrArg Prod.fst (hSame i a y hy.2)
      simpa only [point,incrementsOriginalJointPoint,hId,OpenPartialHomeomorph.refl_symm,
        OpenPartialHomeomorph.refl_apply,id_eq] using hh
    apply (actual_original_native_evaluation_iff Data hd (host a,i.2) _).mpr
    refine ⟨hd.source_inner_norm (host a) _ (hInner a _ hpoint),?_,?_⟩
    · change z.1 ∈ Data.parameterNormDomain i.2
      rw [hp]
      exact hy.1.1.2.2.1
    · change (Data.parameterChart i.2).symm z.1 ∈ Data.parameterSet
      have hh := congrArg Prod.fst (hSame i a y hy.2)
      change (Data.parameterChart i.2).symm z.1 = (point i y).1 at hh
      rw [hh]
      exact hy.1.1.2.2.2
  · intro i a z hz w
    change cF*‖w‖^2 ≤ ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart i.2).symm z.1,x)) ∘
      (e a z.1).symm) z.2 w‖^2
    simpa only [hId i.2,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using hFirst a z hz w
  · intro i a z hz w
    change cT*‖w‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
      (fun x => Data.F ((Data.parameterChart i.2).symm z.1,x))
      (hF ((Data.parameterChart i.2).symm z.1)) (e a z.1).symm z.2 w‖^2
    simpa only [hId i.2,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using hFrame a z hz w
  · intro i a z hz
    change mu ≤ ‖actualOriginalFreeNormalFieldRaw
      (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
      (fun p => hF ((Data.parameterChart i.2).symm p)) (e a)
      (fun z : X => Data.freeNormal nu ((Data.parameterChart i.2).symm z.1,(e a z.1).symm z.2)) z‖
    simpa only [hId i.2,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using hReserve a z hz

end GlobalEmbedding.Continuation
