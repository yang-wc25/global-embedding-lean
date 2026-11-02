import IncrementsCompletion.PositiveSecondaryRawPiece
import Probes.ActualIncrementSecondaryGeometryRestriction
import Probes.ActualIncrementSecondaryChoiceRestriction

/-! Restrict an actual secondary raw piece to one open positive germ.
The original data, charts as functions, inverse, cutoff, phase, numerical
profiles and reserves are retained.  Only chart domains, carrier and sample
sets are restricted.  Its raw producer is the existing actual geometry
producer followed by the proved geometry restriction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

namespace IncrementsCompletionPositiveParameterRawPiece
def restrictOpen
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {hd : IncrementsOriginalDomainConditions Data} {hs : IncrementsOriginalSmoothInputs Data}
  {i : Fin Data.atlas.count × Fin Data.parameterCount}
  {r : ActualSecondarySignedRecord (Fin Data.primaryCount)} {W : Set (Ep × M)}
  {Index : Type*} {observer : Index → OpenPartialHomeomorph M D} {Samples : Index → Set X}
    (old : IncrementsCompletionPositiveParameterRawPiece Data hd hs i r W observer Samples)
    (G : Set (Ep × M)) (hG : IsOpen G) (hGW : G ⊆ W) (hW : IsOpen W) :
    IncrementsCompletionPositiveParameterRawPiece Data hd hs i r G observer Samples := by
  classical
  exact {
    choice := old.choice.restrictOpen G hG
    carrier := G ∩ old.carrier
    sample := old.sample ∩ (old.choice.chart.restrOpen G hG).target
    host_eq := old.host_eq
    cutoff_smooth := old.cutoff_smooth.mono hGW
    carrier_eq := by
      rw [old.carrier_eq]
      ext z
      have hGWz : z ∈ G → z ∈ W := fun hz => hGW hz
      simp only [ActualOriginalSecondaryChoice.restrictOpen,actualOriginalParameterSupportPair,
        parameterRound2_global_relativeSupport_eq W hW,
        parameterRound2_global_relativeSupport_eq G hG,mem_inter_iff]
      tauto
    sample_subset := fun _ hz => hz.2
    carrier_source := fun _ hz => ⟨old.carrier_source hz.2,hz.1⟩
    source_domain := fun _ hz => hz.2
    chart_smooth := old.chart_smooth.mono (fun _ hz => hz.1)
    chart_inverse_smooth := old.chart_inverse_smooth.mono (fun _ hz => hz.1)
    host_source := fun _ hz => old.host_source hz.1
    support := actual_secondary_relative_pair_cutoff_restrict old.choice.cutoff
      (fun z => Data.cutoff r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2))
      (fun z => Data.cutoff r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2))
      W G old.carrier hW hG hGW old.support
    pair := actual_secondary_relative_pair_support_restrict
      (fun z => Data.cutoff r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2))
      (fun z => Data.cutoff r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2))
      W G old.carrier hW hG old.pair
    cut_smooth := old.cut_smooth.mono (fun _ hz => ⟨hz.1,hz.2.1⟩)
    inv_smooth := old.inv_smooth.mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
    host_samples := by
      dsimp only
      rintro z ⟨y,hy,rfl⟩
      exact old.host_samples ⟨y,hy.1,rfl⟩
    observer_samples := by
      intro v z hz
      refine ⟨old.observer_samples v z ⟨hz.1,hz.2.2⟩,?_⟩
      exact (old.choice.chart.restrOpen G hG).map_source
        ⟨old.carrier_source hz.2.2,hz.2.1⟩
    Tinv := old.Tinv
    Kcut := old.Kcut
    Tobs := old.Tobs
    Tinv_nonneg := old.Tinv_nonneg
    Kcut_nonneg := old.Kcut_nonneg
    Tobs_nonneg := old.Tobs_nonneg
    cut_jets := fun ell hell hell1 n k hk z hz => old.cut_jets ell hell hell1 n k hk z hz.1
    inv_jets := fun ell hell hell1 k hk z hz => old.inv_jets ell hell hell1 k hk z hz.1
    observer_jets := fun ell hell hell1 v z hz k hk =>
      old.observer_jets ell hell hell1 v z ⟨hz.1,hz.2.2⟩ k hk
    cT := old.cT
    Bnative := old.Bnative
    cT_pos := old.cT_pos
    Bnative_pos := old.Bnative_pos
    produce := by
      intro n j ell budget c hell hell1 hC hFinite hBudget
      obtain ⟨out,hc,hChart,hPhase,hSample,hSupport⟩ :=
        old.produce n j ell budget c hell hell1 hC hFinite hBudget
      refine ⟨out.restrictOpen G hG hGW,hc,?_,hPhase,?_,?_⟩
      · change out.chart.restrOpen G hG = old.choice.chart.restrOpen G hG
        rw [hChart]
      · change out.sample ∩ (out.chart.restrOpen G hG).target =
          old.sample ∩ (old.choice.chart.restrOpen G hG).target
        rw [hSample,hChart]
      · change G ∩ out.support = G ∩ old.carrier
        rw [hSupport]
  }


theorem restrictOpen_fields
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {hd : IncrementsOriginalDomainConditions Data} {hs : IncrementsOriginalSmoothInputs Data}
  {i : Fin Data.atlas.count × Fin Data.parameterCount}
  {r : ActualSecondarySignedRecord (Fin Data.primaryCount)} {W : Set (Ep × M)}
  {Index : Type*} {observer : Index → OpenPartialHomeomorph M D} {Samples : Index → Set X}
    (old : IncrementsCompletionPositiveParameterRawPiece Data hd hs i r W observer Samples)
    (G : Set (Ep × M)) (hG : IsOpen G) (hGW : G ⊆ W) (hW : IsOpen W) :
    let out := old.restrictOpen G hG hGW hW
    out.choice = old.choice.restrictOpen G hG ∧
    out.carrier = G ∩ old.carrier ∧
    out.sample = old.sample ∩ out.choice.chart.target ∧
    out.Tinv = old.Tinv ∧ out.Kcut = old.Kcut ∧ out.Tobs = old.Tobs ∧
    out.cT = old.cT ∧ out.Bnative = old.Bnative :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end IncrementsCompletionPositiveParameterRawPiece
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.IncrementsCompletionPositiveParameterRawPiece.restrictOpen
#print axioms GlobalEmbedding.Continuation.IncrementsCompletionPositiveParameterRawPiece.restrictOpen_fields
