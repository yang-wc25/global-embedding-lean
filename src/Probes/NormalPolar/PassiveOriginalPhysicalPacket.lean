import NormalPolar.PassiveOriginalParameterPrepared
import NormalPolar.PassiveOriginalFixedGiven
import NormalPolar.PassiveOriginalCompactGivenInput
import Smoothing.ParameterRound2PreparedGeometry

/-! Manufacture the physical fixed smoothing packet from the original
zero-parameter fixed material.  Its actual parameter cutoffs and their
whole-target budgets are constructed together with the initial parameter
atlas.  No physical packet, completed smoothing geometry or Given output
budget is assumed.  The record construction is the same literal one used
by repair_original_actual_smoothing_packet, without its unrelated finite
reference-factory import closure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

def passiveOriginalPhysicalReferenceBudget
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (j : ℕ) : ℝ :=
  (paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet)).toReal

def passiveOriginalPhysicalFixedBudget
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (j : ℕ) : ℝ :=
  (parameterRound2_originalFixedPacketProfile Data j 1).toReal

theorem passiveOriginal_physical_packet_from_same_preparation
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hs : IncrementsOriginalSmoothInputs seed)
    {BS TS BP0 TP0 : ℕ → ℝ} {Ds Dp0 : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference Given : ℕ → ℝ}
    (fixed : Round3RepairFixedSmoothingPacket seed BS TS BP0 TP0 Ds Dp0 radius0 hradius0 reference Given)
    (hzero : (0 : Z) ∈ seed.parameterSet)
    (hReference : seed.F = fixed.referenceMap)
    (hOmega : seed.sourceNormDomain = fixed.Omega) (hQ0 : seed.parameterNormDomain = fixed.Q)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep)
    (hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i)
    (BP TP : ℕ → ℝ) (raw : TensorRawCutoffPreparation B BP TP B.supportDegree) :
    let Data := passiveOriginalData (0 : Z) seed B Q
    ∃ radius : ℝ, ∃ hradius : 0 < radius,
      ∃ packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds B.supportDegree radius hradius
        (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data),
      packet.parameterFamily = tensorChartFamilyOfAtlas B ∧
      packet.referenceMap = (fun z => seed.F (0,z.2)) ∧
      packet.Omega = seed.sourceNormDomain ∧ packet.Q = Q ∧ packet.metric = Data.H ∧
      packet.sourcePreparation.raw = fixed.sourcePreparation.raw := by
  let Data := passiveOriginalData (0 : Z) seed B Q
  have hAll : seed.parameterSet = univ := Set.eq_univ_iff_forall.mpr fun z => by
    simpa only [Subsingleton.elim z (0 : Z)] using hzero
  have hopen := fixed.domain.parameter_subset hzero
  have hInner (i : Fin B.count) (p : P) (hp : p ∈ B.inner i) : B.chart i p ∈ Q i := by
    apply (hQ i).2.2
    apply subset_closure
    apply bufferedInner_subset_sampling B i
    refine ⟨(B.chart i).map_source (B.inner_subset i hp),?_⟩
    change (B.chart i).symm (B.chart i p) ∈ B.inner i
    simpa only [(B.chart i).left_inv (B.inner_subset i hp)] using hp
  let hdP := passiveOriginalData_domain (0 : Z) seed fixed.domain hopen B hB Q
    (fun i => (hQ i).2.1) hInner
  obtain ⟨b0,hb0,hQb0⟩ := fixed.domain.parameter_cover 0 hzero
  have hz : seed.parameterChart b0 0 = (0 : Z) := Subsingleton.elim _ _
  have ht : (0 : Z) ∈ (seed.parameterChart b0).target := hz ▸ (seed.parameterChart b0).map_source hb0
  have hnorm : (0 : Z) ∈ seed.parameterNormDomain b0 := hz ▸ hQb0
  let hsP := passiveOriginalData_smooth (0 : Z) seed hs hopen b0 ht B Q
  have hSeed := passiveOriginal_fixed_reference_given_finite seed fixed hReference hAll hOmega hQ0
  obtain ⟨C,hC,hGiven⟩ := passiveOriginal_given_profile_uniform_cost (0 : Z) seed B Q hdP
    fixed.domain hs b0 ht hnorm hzero hb0 hB hforward (fun i => (hQ i).1) (fun i => (hQ i).2.1)
  have hFinite (j : ℕ) : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤ := by
    apply ne_top_of_le_ne_top (hGiven j 1 le_rfl (hSeed j)).1
    rw [parameterRound2_originalGivenProfile_eq_map_tensor_packet]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have href : Data.H = fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => Data.F (p,y)) x := by
    funext p x
    have h := congrFun (congrFun fixed.reference_tensor (0 : Z)) x
    rw [← hReference] at h
    exact h
  have hrefEq : Data.reference = Data.H := by
    funext p x
    exact congrFun (congrFun fixed.reference_eq (0 : Z)) x
  have hSourceCompact : ∀ i, IsCompact (Data.sourceNormDomain i) := by
    change ∀ i, IsCompact (seed.sourceNormDomain i)
    rw [hOmega]
    exact fixed.source_compact
  have hSourceSampling : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i := by
    change ∀ i, bufferedSamplingCoordinates seed.atlas i ⊆ seed.sourceNormDomain i
    rw [hOmega]
    exact fixed.source_sampling
  let radius := min B.buffer seed.atlas.buffer / 2
  have hradius : 0 < radius := div_pos (lt_min B.buffer_pos seed.atlas.buffer_pos) (by norm_num)
  let packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds B.supportDegree radius hradius
      (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data) := {
    domain := hdP
    parameterFamily := tensorChartFamilyOfAtlas B
    chart_eq := rfl
    sourcePreparation := fixed.sourcePreparation
    parameterPreparation := parameterRound2_localPreparationOfGlobal B raw univ
    buffer := by change min B.buffer seed.atlas.buffer / 2 ≤ min B.buffer seed.atlas.buffer; linarith [B.buffer_pos,seed.atlas.buffer_pos,lt_min B.buffer_pos seed.atlas.buffer_pos]
    Omega := Data.sourceNormDomain
    Q := Q
    source_compact := hSourceCompact
    parameter_compact := fun i => (hQ i).1
    source_target := hdP.source_norm_subset
    parameter_target := fun i => (hQ i).2.1
    source_sampling := hSourceSampling
    parameter_sampling := fun i => (subset_closure.trans (hQ i).2.2)
    samples_compact := parameterRound2_originalEvaluation_univ_compact Data.atlas Data.parameterChart _ _
      hSourceCompact (fun i => (hQ i).1) hdP.source_norm_subset hdP.parameter_norm_subset
    samples_sampling := fun _ => Subset.rfl
    referenceMap := Data.F
    referenceMap_smooth := (parameterRound2_original_full_parameter_coordinates Data hdP hsP rfl).1
    reference_tensor := href
    reference_eq := hrefEq
    reference_bound := by intro j; rw [← href]; exact le_rfl
    given_finite := hFinite
    given_bound := fun _ => le_rfl
    metric := Data.H
    metric_symmetric := by
      rw [href]
      intro p x
      exact (inducedMetric_isPosSemidef (I := 𝓘(ℝ,D)) (fun y => Data.F (p,y)) x).isSymm
    metric_smooth := (parameterRound2_original_full_parameter_coordinates Data hdP hsP rfl).2.2 }
  exact ⟨radius,hradius,packet,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem passiveOriginal_exists_physical_fixed_packet
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hs : IncrementsOriginalSmoothInputs seed)
    {BS TS BP0 TP0 : ℕ → ℝ} {Ds Dp0 : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference Given : ℕ → ℝ}
    (fixed : Round3RepairFixedSmoothingPacket seed BS TS BP0 TP0 Ds Dp0 radius0 hradius0 reference Given)
    (hzero : (0 : Z) ∈ seed.parameterSet)
    (hReference : seed.F = fixed.referenceMap)
    (hOmega : seed.sourceNormDomain = fixed.Omega) (hQ0 : seed.parameterNormDomain = fixed.Q) :
    ∃ B : BufferedAtlas P Ep, IsSmoothBufferedAtlas B ∧
      (∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i)) ∧
      ∃ Q : Fin B.count → Set Ep,
      (∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧ closure (bufferedSamplingCoordinates B i) ⊆ Q i) ∧
      ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
      let Data := passiveOriginalData (0 : Z) seed B Q
      ∃ radius : ℝ, ∃ hradius : 0 < radius,
      ∃ packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds B.supportDegree radius hradius
        (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data),
      packet.parameterFamily = tensorChartFamilyOfAtlas B ∧
      packet.referenceMap = (fun z => seed.F (0,z.2)) ∧
      packet.Omega = seed.sourceNormDomain ∧ packet.Q = Q ∧ packet.metric = Data.H ∧
      packet.sourcePreparation.raw = fixed.sourcePreparation.raw := by
  obtain ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,⟨raw⟩⟩ :=
    passiveOriginal_exists_global_forward_prepared_parameter_atlas (P := P) (d := d)
  exact ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,
    passiveOriginal_physical_packet_from_same_preparation seed hs fixed hzero hReference hOmega hQ0
      B hB hforward Q hQ BP TP raw⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_physical_packet_from_same_preparation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_exists_physical_fixed_packet
