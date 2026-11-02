import NormalPolar.PassiveOriginalPhysicalPacket
import NormalPolar.PassiveOriginalSmallBuffer

/-! The true physical fixed packet is produced after a freely chosen
initial buffer cap.  Charts, inner cover, supports, original Q, raw cutoffs
and every raw budget were fixed before that cap.  Hence the actual source
cost can select the future repair ball without a second atlas choice or a
circular change of its norm.  This is initial input manufacture, not a
shrinking of a ball that has already been specified. -/

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

def passiveOriginal_parameter_raw_small_buffer
    (B : BufferedAtlas P Ep) (BP TP : ℕ → ℝ)
    (raw : TensorRawCutoffPreparation B BP TP B.supportDegree)
    (cap : ℝ) (hcap : 0 < cap) :
    TensorRawCutoffPreparation (passiveOriginalSmallBuffer B cap hcap)
      BP TP (passiveOriginalSmallBuffer B cap hcap).supportDegree where
  raw := raw.raw
  smooth := raw.smooth
  plateau_cover := raw.plateau_cover
  inner_support := raw.inner_support
  enlarged_support := raw.enlarged_support
  degree := raw.degree
  own_jets := raw.own_jets
  transition_jets := raw.transition_jets

theorem passiveOriginal_parameter_raw_small_buffer_fields
    (B : BufferedAtlas P Ep) (BP TP : ℕ → ℝ)
    (raw : TensorRawCutoffPreparation B BP TP B.supportDegree)
    (cap : ℝ) (hcap : 0 < cap) :
    (passiveOriginal_parameter_raw_small_buffer B BP TP raw cap hcap).raw = raw.raw := rfl

theorem passiveOriginal_exists_initialized_physical_fixed_packet
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
      ∀ cap : ℝ, ∀ hcap : 0 < cap,
      let Binit := passiveOriginalSmallBuffer B cap hcap
      let Data := passiveOriginalData (0 : Z) seed Binit Q
      ∃ radius : ℝ, ∃ hradius : 0 < radius,
      ∃ packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Binit.supportDegree radius hradius
        (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data),
      packet.parameterFamily = tensorChartFamilyOfAtlas Binit ∧
      packet.referenceMap = (fun z => seed.F (0,z.2)) ∧
      packet.Omega = seed.sourceNormDomain ∧ packet.Q = Q ∧ packet.metric = Data.H ∧
      packet.sourcePreparation.raw = fixed.sourcePreparation.raw := by
  obtain ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,⟨raw⟩⟩ :=
    passiveOriginal_exists_global_forward_prepared_parameter_atlas (P := P) (d := d)
  refine ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,?_⟩
  intro cap hcap
  exact passiveOriginal_physical_packet_from_same_preparation seed hs fixed hzero hReference hOmega hQ0
    (passiveOriginalSmallBuffer B cap hcap) (passiveOriginalSmallBuffer_smooth B hB cap hcap)
    hforward Q (passiveOriginalSmallBuffer_samples B cap hcap Q hQ) BP TP
    (passiveOriginal_parameter_raw_small_buffer B BP TP raw cap hcap)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_parameter_raw_small_buffer
#print axioms GlobalEmbedding.Continuation.passiveOriginal_exists_initialized_physical_fixed_packet
