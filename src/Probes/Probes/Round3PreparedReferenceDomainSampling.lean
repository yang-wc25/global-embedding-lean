import Probes.Round3PreparedReferenceCarrier

/-! Every fixed reference chart point over K is an actual original host
sample. The proof uses genuine source containment in the original inner
chart, not a restriction to cutoff supports or equality with an open norm set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_prepared_reference_target_samples
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (nu : Fin Data.primaryCount) (a : Β) (z : X)
    (hz : z ∈ (packet.piece nu a).native.target) (hKz : z.1 ∈ Data.parameterSet) :
    parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Data.atlas (packet.piece nu a).host (packet.piece nu a).slices z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet ((packet.piece nu a).host,baseIndex.2) ∧
    ∀ j, ‖iteratedFDeriv ℝ j
      (round3OriginalAdaptedTransition Data.atlas (packet.piece nu a).host (packet.piece nu a).slices) z‖ ≤ packet.Tchart j := by
  let part := packet.piece nu a
  let c := Data.atlas.chart part.host
  let b := part.native
  let e := part.slices
  have hs0 := actual_host_slice_source_point c b _ e part.data z hz
  have hInner := packet.source_inner nu a (z.1,(e z.1).symm z.2) hs0
  constructor
  · apply (actual_original_native_evaluation_iff Data hd (part.host,baseIndex.2) _).mpr
    have hParam : z.1 ∈ Data.parameterNormDomain baseIndex.2 := by
      obtain ⟨ip,hip,hpn⟩ := hd.parameter_cover z.1 hKz
      have hipeq : ip = baseIndex.2 := Fin.ext (by have hi := ip.isLt; have hj := baseIndex.2.isLt; omega)
      rw [hipeq,hId] at hpn
      exact hpn
    refine ⟨hd.source_inner_norm part.host _ hInner,hParam,?_⟩
    change (Data.parameterChart baseIndex.2).symm z.1 ∈ Data.parameterSet
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hKz
  · rcases part.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    intro j
    change ‖iteratedFDeriv ℝ j (actualSourceChartTransition (fun _ => c) e) z‖ ≤ _
    rw [hbj j z hz]
    exact packet.chart_jets_target nu a j z hz

 theorem round3_prepared_native_target_subset
    (b b' : OpenPartialHomeomorph X X)
    (hForward : (b' : X → X) = b) (hSource : b'.source ⊆ b.source) :
    b'.target ⊆ b.target := by
  intro z hz
  have hh := b.map_source (hSource (b'.map_target hz))
  rw [← hForward,b'.right_inv hz] at hh
  exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_target_samples
#print axioms GlobalEmbedding.Continuation.round3_prepared_native_target_subset
