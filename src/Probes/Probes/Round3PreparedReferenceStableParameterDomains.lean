import Probes.Round3PreparedReferenceStableDomains
import Probes.Round3PreparedStablePrimaryDomains
import Probes.Round3PreparedHostParameterRestriction
import Probes.Round3PreparedReferenceDomainSampling

/-! One genuine original C2 tolerance produces stage-dependent stable domains
for the same fixed primary packet. The chart/cutoff functions and all reference
profiles are preserved. No first/frame/normal output certificate is an input. -/
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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance stableFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance stableFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance stableFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance stableFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_prepared_reference_C2_stable_parameter_domains
    {Β : Type*} [Fintype Β] {Rsub : ℕ}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (packet : Round3PreparedReferencePrimaryPacket Data hd hs hn baseIndex Β Rsub)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Data.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : Ep → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => F z.1 z.2-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => F z.1 z.2-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ epsilon →
    ∃ V : Set Ep, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ packet.parameterDomain ∧
    ∃ (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
      (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D),
      (∀ nu a, (b nu a : X → X) = (packet.piece nu a).native) ∧
      (∀ nu a, ((b nu a).symm : X → X) = (packet.piece nu a).native.symm) ∧
      (∀ nu a p, ((e nu a p).symm : D → M) = ((packet.piece nu a).slices p).symm) ∧
      (∀ nu a, (b nu a).source ⊆ (packet.piece nu a).native.source) ∧
      (∀ nu a, (b nu a).target ⊆ (packet.piece nu a).native.target) ∧
      (∀ nu a, (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (b nu a)).source ⊆ V ×ˢ (univ : Set M)) ∧
      (∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (packet.piece nu a).host) (b nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) (e nu a)) ∧
      (∀ nu a, incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M)) (packet.piece nu a).cutoff ⊆
        (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (b nu a)).source) ∧
      (∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu a).host) (b nu a)).source →
        ((Data.parameterChart baseIndex.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu a z, z ∈ (b nu a).target → ∀ v : D,
        (packet.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e nu a z.1).symm) z.2 v‖^2) ∧
      (∀ nu a z, z ∈ (b nu a).target → ∀ v : Tdata,
        (packet.cT/16)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e nu a z.1).symm z.2 v‖^2) ∧
      ∀ nu a z, z ∈ (b nu a).target → (1/4 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F z.1 ∘ (e nu a z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e nu a z.1).symm z.2)
        (Data.freeNormal nu ((Data.parameterChart baseIndex.2).symm z.1,(e nu a z.1).symm z.2))‖ := by
  obtain ⟨epsilon,hepsilon,hStable⟩ := round3_prepared_reference_C2_stable_domains
    Data hd hs hn baseIndex hId hOne packet hF0joint
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound
  obtain ⟨V,hV,hKV,hVV,b0,e0,hb0,hbi0,he0,hSource0,hdata0,hSupport0,hActive0,hFirst0,hFrame0,hNormal0⟩ :=
    hStable F hFjoint hF hFinite hBound
  have hEach (nu : Fin Data.primaryCount) (a : Β) := round3_prepared_host_restrict_parameter
    (Data.atlas.chart (packet.piece nu a).host) (hd.atlas_smooth.chart_mem (packet.piece nu a).host)
    (b0 nu a) _ (e0 nu a) (hdata0 nu a) V hV
  choose b e hdata hSource hTarget hb hbi he hASource using hEach
  refine ⟨V,hV,hKV,hVV,b,e,?_,?_,?_,?_,?_,?_,hdata,?_,?_,?_,?_,?_⟩
  · intro nu a
    exact (hb nu a).trans (hb0 nu a)
  · intro nu a
    exact (hbi nu a).trans (hbi0 nu a)
  · intro nu a p
    exact (he nu a p).trans (he0 nu a p)
  · intro nu a
    exact (hSource nu a).trans (hSource0 nu a)
  · intro nu a z hz
    rw [hTarget] at hz
    exact round3_prepared_native_target_subset (packet.piece nu a).native (b0 nu a)
      (hb0 nu a) (hSource0 nu a) hz.1
  · intro nu a
    rw [hASource]
    exact inter_subset_right
  · intro nu a y hy
    rw [hASource]
    refine ⟨hSupport0 nu a hy,?_⟩
    rw [parameterRound2_global_relativeSupport_eq _ (hV.prod isOpen_univ)] at hy
    exact hy.1
  · intro nu a y hy
    rw [hASource] at hy
    exact hActive0 nu a y hy.1
  · intro nu a z hz v
    rw [he]
    exact hFirst0 nu a z (by rw [hTarget] at hz; exact hz.1) v
  · intro nu a z hz v
    rw [he]
    exact hFrame0 nu a z (by rw [hTarget] at hz; exact hz.1) v
  · intro nu a z hz
    rw [he]
    exact hNormal0 nu a z (by rw [hTarget] at hz; exact hz.1)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_C2_stable_parameter_domains
