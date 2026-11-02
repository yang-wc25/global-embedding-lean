import Smoothing.Round3OuterHostNormalCover
import Probes.Round3ParameterCrossNativeData
import Probes.ActualIncrementOriginalPrimitiveBinding

/-! Genuine normal-cover producer for arbitrary parameter manifolds and
nonlinear parameter charts. Canonical cross-chart slice packets determine
all observer maps, original samples and physical-point identities. No
identity parameter chart or Euclidean parameter-manifold hypothesis enters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
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

def round3OriginalNativeObserverPoint
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Y) : Ep × M :=
  (incrementsOriginalParameterPoint y,(Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y))

theorem round3_original_native_observer_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3OriginalNativeObserverPoint Data i) (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) := by
  have hp : ContMDiff 𝓘(ℝ,Y) 𝓘(ℝ,Ep) ∞ incrementsOriginalParameterPoint :=
    (parameterTensorModelEquiv (m+1) d).symm.contDiff.fst.contMDiff
  have hx : ContMDiff 𝓘(ℝ,Y) 𝓙 ∞ incrementsOriginalSourcePoint :=
    (parameterTensorModelEquiv (m+1) d).symm.contDiff.snd.contMDiff
  exact hp.contMDiffOn.prodMk
    ((contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
      hx.contMDiffOn (fun _ hy => hy.1))

def round3ParameterHostNormalCover
    {A : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (nu : Fin Data.primaryCount) (domain : Set (P × M))
    (host : Fin Data.parameterCount → A → Fin Data.atlas.count)
    (b : Fin Data.parameterCount → A → OpenPartialHomeomorph X X)
    (e : Fin Data.parameterCount → A → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ ip a, ActualOriginalHostSliceData (Data.atlas.chart (host ip a)) (b ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e ip a))
    (hNative : ∀ ip a, (b ip a).source ⊆ actualOriginalNativeOpen Data (host ip a,ip))
    (hActive : ∀ ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hInner : ∀ ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source →
      w.2 ∈ Data.atlas.inner (host ip a))
    (carrier : Fin Data.parameterCount → A → Set (Ep × M))
    (hCarrierOpen : ∀ ip a, IsOpen (carrier ip a))
    (hCarrierSub : ∀ ip a, carrier ip a ⊆ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source)
    (hCover : ∀ ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ domain →
      ∃ a, w ∈ carrier ip a)
    (cF cT mu : ℝ)
    (hFirst : ∀ ip a z, z ∈ (b ip a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart ip).symm z.1,x)) ∘ (e ip a z.1).symm) z.2 w‖^2)
    (hFrame : ∀ ip a z, z ∈ (b ip a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (e ip a z.1).symm z.2 w‖^2)
    (hReserve : ∀ ip a z, z ∈ (b ip a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
        (fun p => hF ((Data.parameterChart ip).symm p)) (e ip a)
        (fun z : X => Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e ip a z.1).symm z.2)) z‖) :
    Round3OriginalNormalCoverGeometry Data hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu) A
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (fun i => incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ∩
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹' domain) cF cT mu := by
  let chart := fun ip a => actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)
  let point := round3OriginalNativeObserverPoint Data
  let U := fun i a => incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
    point i ⁻¹' carrier i.2 a
  let forward := fun i a => chart i.2 a ∘ point i
  let native := fun ip a => (b ip a).target ∩ (chart ip a).symm ⁻¹' carrier ip a
  have hPoint (i) := round3_original_native_observer_smooth Data hd i
  have hU (i) (a : A) : IsOpen (U i a) :=
    (hPoint i).continuousOn.isOpen_inter_preimage
      (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i) (hCarrierOpen i.2 a)
  have hNativeOpen (ip) (a : A) : IsOpen (native ip a) := by
    have hh := (chart ip a).continuousOn_symm.isOpen_inter_preimage
      (chart ip a).open_target (hCarrierOpen ip a)
    change IsOpen ((b ip a).target ∩ (chart ip a).symm ⁻¹' carrier ip a)
    rwa [(hData ip a).1] at hh
  have hMapFull (i) (a : A) : MapsTo (forward i a) (U i a) (b i.2 a).target := by
    intro y hy
    rw [← (hData i.2 a).1]
    exact (chart i.2 a).map_source (hCarrierSub i.2 a hy.2)
  have hMap (i) (a : A) : MapsTo (forward i a) (U i a) (native i.2 a) := by
    intro y hy
    refine ⟨hMapFull i a hy,?_⟩
    change (chart i.2 a).symm (chart i.2 a (point i y)) ∈ carrier i.2 a
    rw [(chart i.2 a).left_inv (hCarrierSub i.2 a hy.2)]
    exact hy.2
  have hSameNative (i) (a : A) (y : Y) (hy : y ∈ U i a) :
      ((forward i a y).1,(e i.2 a (forward i a y).1).symm (forward i a y).2) = point i y := by
    rcases hData i.2 a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    exact (hpair _ (hMapFull i a hy)).symm.trans ((chart i.2 a).left_inv (hCarrierSub i.2 a hy.2))
  have hSame (i) (a : A) (y : Y) (hy : y ∈ U i a) :
      ((Data.parameterChart i.2).symm (forward i a y).1,
        (e i.2 a (forward i a y).1).symm (forward i a y).2) =
      incrementsOriginalJointPoint Data.atlas Data.parameterChart i y := by
    exact congrArg (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) (hSameNative i a y hy)
  have hGeometry (ip) (a : A) := actual_host_slice_geometry_inputs
    (Data.atlas.chart (host ip a)) (hd.atlas_smooth.chart_mem (host ip a)) (b ip a) _ (e ip a) (hData ip a)
  have hParameter (ip) (a : A) (z : X) (hz : z ∈ (b ip a).target) :
      z.1 ∈ (Data.parameterChart ip).target := by
    have hh := (hGeometry ip a).2.2.2.2.2.2.1 hz
    exact ((round3Parameter_originalNativeOpen_iff Data (host ip a,ip) _).mp (hNative ip a hh)).2.1
  have hNormal (ip) (a : A) : ContDiffOn ℝ ∞
      (fun z : X => Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e ip a z.1).symm z.2))
      (b ip a).target := by
    have hPull := actual_original_parameter_pullback_smooth Data hd ip (Data.freeNormal nu)
      (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) (hs.normal_joint nu)
      (chart ip a).source
      (by
        intro w hw
        have hh := (round3Parameter_originalNativeOpen_iff Data (host ip a,ip) _).mp (hNative ip a hw.2)
        exact hh.2.1)
      (hActive ip a)
    rcases hData ip a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    have hh := (hPull.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ (b ip a).target) => (chart ip a).map_target (by rwa [hat]))).contDiffOn
    apply hh.congr
    intro z hz
    exact congrArg (fun w : Ep × M => Data.freeNormal nu ((Data.parameterChart ip).symm w.1,w.2))
      (hpair z hz).symm
  refine {
    host := fun i a => (host i.2 a,i.2)
    chart := fun i a => e i.2 a
    native := fun i a => native i.2 a
    original := U
    forward := forward
    original_open := hU
    native_open := fun i a => hNativeOpen i.2 a
    original_subset := fun _ _ _ hy => hy.1
    covers := ?_
    chart_smooth := fun i a => (hData i.2 a).2.2.2.2.1
    forward_smooth := ?_
    forward_maps := hMap
    same_point := hSame
    chart_target := fun i a z hz => ((hGeometry i.2 a).2.2.2.1 z hz.1).1
    source := fun i a z hz => ((hGeometry i.2 a).2.2.2.1 z hz.1).2
    parameter := fun i a z hz => hParameter i.2 a z hz.1
    transition_smooth := fun i a => ((hGeometry i.2 a).2.2.2.2.1).mono inter_subset_left
    phase_smooth := ?_
    phase_adapted := fun i a z hz => (hGeometry i.2 a).2.2.2.2.2.2.2 z hz.1
    reference_smooth := fun i a => (hNormal i.2 a).mono inter_subset_left
    sample := ?_
    first := fun i a z hz => hFirst i.2 a z hz.1
    transverse := fun i a z hz => hFrame i.2 a z hz.1
    reserve := fun i a z hz => hReserve i.2 a z hz.1 }
  · intro i y hy
    obtain ⟨a,ha⟩ := hCover i.2 (point i y) hy.1.1.2 hy.2
    exact ⟨a,hy.1.1,ha⟩
  · intro i a
    exact (((hData i.2 a).2.1).comp ((hPoint i).mono inter_subset_left)
      (fun _ hy => hCarrierSub i.2 a hy.2)).contDiffOn
  · intro i a z hz
    exact actual_original_phase_mdifferentiableAt Data hd hs nu _ _
      (hActive i.2 a _ (actual_host_slice_source_point _ _ _ _ (hData i.2 a) z hz.1))
  · intro i a y hy
    let z := forward i a y
    have hz : z ∈ (b i.2 a).target := hMapFull i a hy.2
    have hpoint := actual_host_slice_source_point _ _ _ _ (hData i.2 a) z hz
    have hp : z.1 = incrementsOriginalParameterPoint y := congrArg Prod.fst (hSameNative i a y hy.2)
    apply (actual_original_native_evaluation_iff Data hd (host i.2 a,i.2) _).mpr
    refine ⟨hd.source_inner_norm (host i.2 a) _ (hInner i.2 a _ hpoint),?_,?_⟩
    · change z.1 ∈ Data.parameterNormDomain i.2
      rw [hp]
      exact hy.1.1.2.2.1
    · change (Data.parameterChart i.2).symm z.1 ∈ Data.parameterSet
      rw [hp]
      exact hy.1.1.2.2.2

#print axioms round3ParameterHostNormalCover
end GlobalEmbedding.Continuation
