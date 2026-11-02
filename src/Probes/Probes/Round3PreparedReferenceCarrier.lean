import Probes.Round3PreparedReferencePrimaryPacket
import Smoothing.Round3OuterC2NativeJets
import Probes.ActualIncrementOriginalFamilyKernel

/-! The fixed reference carrier is an actual original sample, and the actual
reference normal supplies the required unit beta-kernel vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_reference_carrier_sampling
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (nu : Fin Data.primaryCount) (a : Β) (y : Ep × M)
    (hy : y ∈ tsupport (packet.piece nu a).cutoff) (hKy : y.1 ∈ Data.parameterSet) :
    let part := packet.piece nu a
    let z := actualHostAdaptedChart (Data.atlas.chart part.host) part.native y
    parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Data.atlas part.host part.slices z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (part.host,baseIndex.2) ∧
    ∀ j, ‖iteratedFDeriv ℝ j (round3OriginalAdaptedTransition Data.atlas part.host part.slices) z‖ ≤ packet.Tchart j := by
  intro part z
  let c := Data.atlas.chart part.host
  let b := part.native
  let aa := actualHostAdaptedChart c b
  have hys : y ∈ aa.source := part.support hy
  rcases part.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hz : z ∈ b.target := by rw [← hat]; exact aa.map_source hys
  have hzp : z.1 = y.1 := (hforw y hys).1
  have hZK : z.1 ∈ Data.parameterSet := hzp ▸ hKy
  constructor
  · have hpy : (part.slices z.1).symm z.2 = y.2 := by
      have hh := aa.left_inv hys
      rw [hpair z hz] at hh
      exact congrArg Prod.snd hh
    apply (actual_original_native_evaluation_iff Data hd (part.host,baseIndex.2) _).mpr
    have hParam : z.1 ∈ Data.parameterNormDomain baseIndex.2 := by
      obtain ⟨ip,hip,hpn⟩ := hd.parameter_cover z.1 hZK
      have hipeq : ip = baseIndex.2 := Fin.ext (by have hi := ip.isLt; have hj := baseIndex.2.isLt; omega)
      rw [hipeq,hId] at hpn
      exact hpn
    refine ⟨?_,hParam,?_⟩
    · change Data.atlas.chart part.host ((part.slices z.1).symm z.2) ∈ Data.sourceNormDomain part.host
      rw [hpy]
      exact hd.source_inner_norm part.host _ (packet.inner nu a y hy)
    · change (Data.parameterChart baseIndex.2).symm z.1 ∈ Data.parameterSet
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hZK
  · intro j
    change ‖iteratedFDeriv ℝ j (actualSourceChartTransition (fun _ => c) part.slices) z‖ ≤ _
    rw [hbj j z hz]
    exact packet.chart_jets nu a j y hy

private theorem round3_reference_normal_transport
    (f g : M → Ey) (hf : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ f) (hg : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ g)
    (hfg : f = g) (chart : D → M) (x : D) (v : Ey)
    (h : ∃ normal : normalSpace (I := 𝓙) f (chart x),
      (normal : Ey) = v ∧ ‖normal‖ = 1 ∧ incrementsTransversePairing f hf
        (chart x) (fun a : Fin m => incrementsModeCoordinateDirections chart x a.succ) normal = 0) :
    ∃ normal : normalSpace (I := 𝓙) g (chart x),
      (normal : Ey) = v ∧ ‖normal‖ = 1 ∧ incrementsTransversePairing g hg
        (chart x) (fun a : Fin m => incrementsModeCoordinateDirections chart x a.succ) normal = 0 := by
  cases hfg
  exact h

theorem round3_prepared_primary_reference_normal
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (nu : Fin Data.primaryCount) (a : Β)
    (z : X) (hz : z ∈ (packet.piece nu a).native.target)
    (hF0 : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x))) :
    ∃ normal : normalSpace (I := 𝓙) (fun x => Data.F (z.1,x)) (((packet.piece nu a).slices z.1).symm z.2),
      (normal : Ey) = Data.freeNormal nu (z.1,((packet.piece nu a).slices z.1).symm z.2) ∧
      ‖normal‖ = 1 ∧
      incrementsTransversePairing (fun x => Data.F (z.1,x)) hF0
        (((packet.piece nu a).slices z.1).symm z.2)
        (fun a' : Fin m => incrementsModeCoordinateDirections ((packet.piece nu a).slices z.1).symm z.2 a'.succ) normal = 0 := by
  let part := packet.piece nu a
  let F0 := actualOriginalOpenParameterSlice Data baseIndex
  let hOld := actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex
  let host := fun nu a => (packet.piece nu a).host
  let b := fun nu a => (packet.piece nu a).native
  let e := fun nu a => (packet.piece nu a).slices
  let hdata := fun nu a => (packet.piece nu a).data
  let eta := fun nu a => (packet.piece nu a).cutoff
  let active := fun nu a => (packet.piece nu a).active
  let g := actualOriginalPrimaryFamily Data hd hs hn baseIndex host b e hdata eta active
  have hzt : z ∈ (g.chart nu a).target := by
    change z ∈ (actualHostAdaptedChart (Data.atlas.chart part.host) part.native).target
    rw [(part.data).1]
    exact hz
  have hs0 := actual_host_slice_source_point (Data.atlas.chart part.host) part.native _ part.slices part.data z hz
  have hact := part.active _ hs0
  have hEq : F0 z.1 = fun x => Data.F (z.1,x) := by
    funext x
    change actualOriginalOpenParameterSlice Data baseIndex z.1 x = _
    rw [actualOriginalOpenParameterSlice_eq Data baseIndex z.1 hact.2.1]
    change Data.F ((Data.parameterChart baseIndex.2).symm z.1,x) = _
    rw [hId]
    rfl
  have hWitness : ∃ normal : normalSpace (I := 𝓙) (F0 z.1) ((e nu a z.1).symm z.2),
      (normal : Ey) = Data.freeNormal nu (z.1,(e nu a z.1).symm z.2) ∧ ‖normal‖ = 1 ∧
      incrementsTransversePairing (F0 z.1) (hOld z.1) ((e nu a z.1).symm z.2)
        (fun a' : Fin m => incrementsModeCoordinateDirections (e nu a z.1).symm z.2 a'.succ) normal = 0 := by
    refine ⟨⟨g.normal nu (z.1,g.inverse nu a z.1 z.2),g.normal_mem nu a z hzt⟩,?_,?_,?_⟩
    · change Data.freeNormal nu ((Data.parameterChart baseIndex.2).symm z.1,(e nu a z.1).symm z.2) = _
      rw [hId]
      rfl
    · exact actualOriginalPrimaryFamily_normal_unit Data hd hs hn baseIndex host b e hdata eta active nu a z hzt
    · exact actualOriginalPrimaryFamily_normal_kernel Data hd hs hn baseIndex host b e hdata eta active nu a z hzt
  exact round3_reference_normal_transport (F0 z.1) (fun x => Data.F (z.1,x))
    (hOld z.1) hF0 hEq (e nu a z.1).symm z.2 _ hWitness

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_carrier_sampling
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_reference_normal
