import Repair.EntranceUniformPhaseFactory
import Probes.Round3RepairLimitPhase
import Smoothing.Round3RepairInitialState
import Smoothing.Round3RepairParameterPhaseFactory

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped Classical ContDiff ENNReal Topology BigOperators
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
private local instance entranceUniformLimitPhaseChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance entranceUniformLimitPhaseIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










variable [T2Space M]

/-- The exact numerical phase tolerance is the minimum of the two reference
geometry thresholds of the same selected primary and secondary packets.
The actual series limit is tested in the original C2 norm; no later
phase radius, phase packet or limiting Good predicate is supplied. -/
theorem repairEntrance_uniform_limit_phase_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (hReference : packet.referenceMap = Data.F)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data packet.domain hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (primary : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data packet.domain hs theta primary)
    (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (primary.piece nu i a).cutoff →
      y.1 ∈ Data.parameterNormDomain i.2)
    (secondary : Round3PreparedParameterSecondaryPacket Data packet.domain hs theta)
    (hSecondaryParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier →
      y.1 ∈ Data.parameterNormDomain i.2)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirstValue : ∀ r i a, (secondary.piece r i a).cF = cF)
    (hFrameValue : ∀ r i a, (secondary.piece r i a).cT = cT)
    (hHessianBound : ∀ r i a, (secondary.piece r i a).MH ≤ MH)
    (hInverseBound : ∀ r i a j, 1 ≤ j → j ≤ 2 → (secondary.piece r i a).Tinv j ≤ T j)
    (R : ℕ) (hPart : ∀ z, ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M)) :
    ∃ phaseEpsilon : ℝ, 0 < phaseEpsilon ∧
      phaseEpsilon = min
        (repairEntranceGeometryTolerance m d N profiles.Tinv profiles.cF profiles.cT profiles.MH
          profiles.cF_pos profiles.cT_pos)
        (repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT) ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∀ {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
      {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
      {initial : Round3RepairClosedState changed budget epsilon eta 10 t}
      (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost Cs sigma budget epsilon eta t ht ht1 initial),
      Round3RepairFullEndpoint changed run → epsilon ≤ phaseEpsilon →
      Round3RepairActualLimitPhase changed run := by
  have hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ Data.F := by
    simpa only [modelWithCornersSelf_prod,hReference] using packet.referenceMap_smooth
  let epsilonP := repairEntranceGeometryTolerance m d N profiles.Tinv
    profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos
  let epsilonS := repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT
  let phaseEpsilon := min epsilonP epsilonS
  have hPhase : 0 < phaseEpsilon := lt_min
    (repairEntranceGeometryTolerance_pos m d N profiles.Tinv profiles.Tinv_nonneg
      profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos profiles.MH_nonneg)
    (repairEntranceGeometryTolerance_pos m d N T hT cF cT MH hcF hcT hMH)
  have hFactory := repairEntrance_uniform_original_phase_factory Data packet.domain hs hn
    hF0joint hK theta primary profiles hPrimaryParam secondary hSecondaryParam T hT cF cT MH
    hcF hcT hMH hFirstValue hFrameValue hHessianBound hInverseBound R hPart hCount hSupport
  refine ⟨phaseEpsilon,hPhase,rfl,?_⟩
  intro metric hSym hSmooth changed cost Cs sigma budget epsilon eta t ht ht1 initial run out heps
  let Fstar := fun z => initial.map z+∑' j, run.increment changed j z
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ Fstar := by
    simpa only [modelWithCornersSelf_prod] using out.limit.2.1
  have hF : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => Fstar (p,x)) :=
    fun p => hFjoint.comp (contMDiff_const.prodMk contMDiff_id)
  have hNorm : paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (fun z => Fstar z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) = changed.mapDistance Fstar := by
    change _ = packet.mapDistance Fstar
    simp only [Round3RepairFixedSmoothingPacket.mapDistance,
      Round3RepairFixedSmoothingPacket.closedSamples,packet.chart_eq,hOmega,hQ,hK,hReference]
  have hSmall : (changed.mapDistance Fstar).toReal ≤ phaseEpsilon := by
    have hBound := out.limit.2.2.2.2.2
    change (changed.mapDistance Fstar).toReal < 3*epsilon/8 at hBound
    linarith
  exact hFactory (fun p x => Fstar (p,x)) hFjoint hF
    (by rw [hNorm]; exact out.limit.2.2.2.2.1)
    (by rw [hNorm]; exact hSmall)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_limit_phase_before_metric
