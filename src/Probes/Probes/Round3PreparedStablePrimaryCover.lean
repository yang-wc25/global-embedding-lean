import Probes.Round3PreparedReferencePrimaryPacket

/-! The actual stable chart domains cover the original cutoff support on
its new parameter neighborhood. Thus the physical primary domain can be
restricted without changing the original phase, cutoff or linear argument.
The cover comes from the true germ partition of the constructed packet. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

def round3PreparedStablePrimaryDomain {Β : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X) (V : Set Ep)
    (nu : Fin Data.primaryCount) : Set (Ep × M) :=
  ⋃ a : Β, (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source ∩
    (V ×ˢ (univ : Set M))

theorem round3_prepared_stable_primary_cover
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (V : Set Ep) (hV : IsOpen V) (hVV0 : V ⊆ packet.parameterDomain)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (hSupport : ∀ nu a, incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M)) (packet.piece nu a).cutoff ⊆
      (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (b nu a)).source)
    (hActive : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (b nu a)).source →
      ((Data.parameterChart baseIndex.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    let host := fun nu a => (packet.piece nu a).host
    let domain := round3PreparedStablePrimaryDomain Data host b V
    ∀ nu, IsOpen (domain nu) ∧ domain nu ⊆ Data.primaryDomain nu ∩ (V ×ˢ (univ : Set M)) ∧
      incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M)) (Data.cutoff nu) ⊆ domain nu ∧
      ∀ y ∈ domain nu, ∃ a, y ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source := by
  intro host domain nu
  have hW := hV.prod (isOpen_univ : IsOpen (univ : Set M))
  refine ⟨isOpen_iUnion (fun a => (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).open_source.inter hW),?_,?_,?_⟩
  · intro y hy
    obtain ⟨a,ha,hv⟩ := mem_iUnion.mp hy
    have hh := (hActive nu a y ha).1
    have hOld : y ∈ Data.primaryDomain nu := by
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hh
    exact ⟨hOld,hv⟩
  · intro y hy
    have hyW : y ∈ V ×ˢ (univ : Set M) := by
      rw [parameterRound2_global_relativeSupport_eq _ hW] at hy
      exact hy.1
    have hSamples := packet.samples 1 (by norm_num) (by norm_num) (V ×ˢ (univ : Set M)) hW
      (fun y hy => ⟨hVV0 hy.1,hy.2⟩)
    have hχ : (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) = Data.cutoff nu := by
      funext z
      rw [hId]
      rfl
    have hyp : y ∈ incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M))
        (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) := by
      rwa [hχ]
    have hSum := (hSamples.partition nu y hyp).self_of_nhds
    change (∑ a, (packet.piece nu a).cutoff y) = 1 at hSum
    have hSome : ∃ a, (packet.piece nu a).cutoff y ≠ 0 := by
      by_contra! hh
      simp only [hh,Finset.sum_const_zero] at hSum
      norm_num at hSum
    obtain ⟨a,ha⟩ := hSome
    apply mem_iUnion.mpr
    refine ⟨a,?_,hyW⟩
    apply hSupport nu a
    rw [parameterRound2_global_relativeSupport_eq _ hW]
    exact ⟨hyW,subset_tsupport _ ha⟩
  · intro y hy
    obtain ⟨a,ha,hv⟩ := mem_iUnion.mp hy
    exact ⟨a,ha⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_stable_primary_cover
