import Probes.Round3PreparedReferenceC2Pointwise
import Probes.Round3PreparedStablePrimaryDomains

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

theorem round3_prepared_reference_C2_stable_domains
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
  obtain ⟨epsilon,hepsilon,hPointwise⟩ := round3_prepared_reference_C2_pointwise
    Data hd hs hn baseIndex hId hOne packet hF0joint
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound
  have hh := round3_prepared_primary_stable_domains Data hd hs baseIndex.2 hId
    (Data.parameterOpen ×ˢ (univ : Set M)) packet.piece Data.parameterSet packet.parameterDomain
    packet.parameter_open packet.parameter_contains F hF hFjoint.contMDiffOn
    (packet.cF/4) (packet.cT/4) (1/2) (div_pos packet.cF_pos (by norm_num))
    (div_pos packet.cT_pos (by norm_num)) (by norm_num)
    (hPointwise F hFjoint hF hFinite hBound)
  simpa only [div_div,show (4:ℝ)*4=16 by norm_num,show (2:ℝ)*2=4 by norm_num] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_reference_C2_stable_domains
