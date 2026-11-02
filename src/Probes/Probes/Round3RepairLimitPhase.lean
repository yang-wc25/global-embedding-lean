import Probes.Round3RepairSmoothMetricEndpoint
import Smoothing.Round3RepairParameterPhaseFactory

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairLimitPhaseChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairLimitPhaseIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










variable [T2Space M]

/-- Full original phase conditions for the SAME actual series limit, on a
true common carrier covering every original cutoff support. -/
def Round3RepairActualLimitPhase [CompactSpace M]
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) : Prop :=
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∃ domain : Fin Data.primaryCount → Set (P × M),
      (∀ nu, domain nu ⊆ Data.primaryDomain nu) ∧
      (∀ nu, tsupport (Data.cutoff nu) ⊆ domain nu) ∧
      let E : IncrementsOriginalNativeData (m+1) d N M P :=
        {Data with F := Fstar, primaryDomain := domain}
      ∃ hdE : IncrementsOriginalDomainConditions E,
      ∃ hsE : IncrementsOriginalSmoothInputs E,
        IncrementsOriginalPhaseConditions E hdE hsE

/-- The original reference packet chooses the phase tolerance before any
repair trajectory. The proved strict original C2 bound for the actual
series supplies it; no limiting Good predicate is an input. -/
theorem round3_repair_actual_limit_phase_tolerance [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (hReference : packet.referenceMap = Data.F)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data packet.domain hs)
    (hn : IncrementsOriginalFreeNormalConditions Data packet.domain hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    ∃ phaseEpsilon : ℝ, 0 < phaseEpsilon ∧
    ∀ {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
      {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
      {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
      (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet cost Cs sigma budget epsilon eta t ht ht1 initial),
      Round3RepairFullEndpoint packet run → epsilon ≤ phaseEpsilon →
      Round3RepairActualLimitPhase packet run := by
  have hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ Data.F := by
    simpa only [modelWithCornersSelf_prod,hReference] using packet.referenceMap_smooth
  have hOmegaC : ∀ i, IsCompact (Data.sourceNormDomain i) := by
    rw [hOmega]
    exact packet.source_compact
  have hQC : ∀ i, IsCompact (Data.parameterNormDomain i) := by
    rw [hQ]
    exact packet.parameter_compact
  have hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i := by
    rw [hOmega]
    exact packet.source_sampling
  have hParameter : ∀ i, tensorLocalSamplingCoordinates packet.parameterFamily i ⊆ Data.parameterNormDomain i := by
    rw [hQ]
    exact packet.parameter_sampling
  obtain ⟨phaseEpsilon,hPhase,hFactory⟩ :=
    round3_repair_original_parameter_phase_factory Data packet.domain hs hp hn hImm hF0joint hK
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp packet.parameterFamily packet.chart_eq
      packet.sourcePreparation packet.parameterPreparation hOmegaC hQC hSource hParameter
  refine ⟨phaseEpsilon,hPhase,?_⟩
  intro cost Cs sigma budget epsilon eta t ht ht1 initial run out heps
  let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ Fstar := by
    simpa only [modelWithCornersSelf_prod] using out.limit.2.1
  have hF : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => Fstar (p,x)) :=
    fun p => hFjoint.comp (contMDiff_const.prodMk contMDiff_id)
  have hNorm : paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => Fstar z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) = packet.mapDistance Fstar := by
    simp only [Round3RepairFixedSmoothingPacket.mapDistance,
      Round3RepairFixedSmoothingPacket.closedSamples,packet.chart_eq,hOmega,hQ,hK,hReference]
  have hSmall : (packet.mapDistance Fstar).toReal ≤ phaseEpsilon := by
    have hBound := out.limit.2.2.2.2.2
    change (packet.mapDistance Fstar).toReal < 3*epsilon/8 at hBound
    linarith
  exact hFactory (fun p x => Fstar (p,x)) hFjoint hF
    (by rw [hNorm]; exact out.limit.2.2.2.2.1)
    (by rw [hNorm]; exact hSmall)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_actual_limit_phase_tolerance
