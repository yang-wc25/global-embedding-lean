import Repair.EntrancePublic
import Repair.EntranceCanonicalConstructed

/-! The full original public conclusion retains the preselected numerical
entry, epsilon and eta in the exact initial scale and C440 radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

private local instance entrancePublicSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem RepairCanonicalEnvelopeConstructedRepair.original_conclusion
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (envelope : ℕ → ℝ) (entry fixedEpsilon fixedEta C2 C442 : ℝ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary)
    [Fintype Β] [Fintype SubSecondary] (Lprimary : ℕ) (tolerance : ℝ)
    (h : RepairCanonicalEnvelopeConstructedRepair Ref smoothing envelope entry fixedEpsilon fixedEta
      C2 C442 Β SubSecondary Lprimary tolerance) :
    ∃ t0 targetRadius : ℝ, 0 < t0 ∧ t0 < 1 ∧ 0 < targetRadius ∧
    t0 = repairEntranceScale (4*(repairEntranceLowFromMap (m+1) d N C2+1)) fixedEpsilon entry
      (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442) ∧
    targetRadius = repairEntranceMetricRadius t0 (4*(repairEntranceLowFromMap (m+1) d N C2+1)) fixedEta ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Ref.atlas
        smoothing.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i))
      (hPositive : ∀ p x, ∀ v : TangentSpace 𝓙 x, v ≠ 0 → 0 < metric p x v v),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun p x => metric p x-Ref.H p x))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart) smoothing.closedSamples ≤
        ENNReal.ofReal targetRadius →
    ∃ (Fstar : P × M → Ey) (G u : ℕ → P × M → Ey) (stage : ℕ → ℕ),
      RepairOriginalLimitConclusion Ref smoothing metric tolerance t0 Fstar G u stage := by
  rcases h with
    ⟨budget,epsilon,eta,hb,he,het,hr,hEpsExact,hEtaExact,hBudget,profile,Ctarget,hCtarget,hL,hCompleted,
      cost,Cs,sigma,hCosts,hCsExact,cap,hCap,hCapExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,
      t0,ht0,ht1,htEntry,hTExact,targetRadius,hRadius,hRadiusExact,hFinish⟩
  have hTUniform : t0 = repairEntranceScale (4*(repairEntranceLowFromMap (m+1) d N C2+1)) fixedEpsilon entry
      (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442) := by
    simpa only [hBudget,hEpsExact] using hTExact
  have hRadiusUniform : targetRadius = repairEntranceMetricRadius t0
      (4*(repairEntranceLowFromMap (m+1) d N C2+1)) fixedEta := by
    simpa only [hBudget,hEtaExact] using hRadiusExact
  refine ⟨t0,targetRadius,ht0,ht1,hRadius,hTUniform,hRadiusUniform,?_⟩
  intro metric hSym hSmooth hPositive hError
  let changed := smoothing.withMetric metric hSym hSmooth
  obtain ⟨initial,hInitial,hInitialDefect,run,out⟩ := hFinish metric hSym hSmooth hPositive hError
  let Fstar := fun z => initial.map z+∑' j, run.increment changed j z
  have hFstar : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ Fstar := out.smooth_metric.full.limit.2.1
  have hProduct : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Fstar := by
    simpa only [modelWithCornersSelf_prod] using hFstar
  have hBound : (changed.mapDistance Fstar).toReal < tolerance := by
    have hh := out.smooth_metric.full.limit.2.2.2.2.2
    change (changed.mapDistance Fstar).toReal < 3*epsilon/8 at hh
    linarith
  have hNorm : changed.mapDistance Fstar =
      paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        (fun z => Fstar z-Ref.F z))
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
        smoothing.closedSamples := by
    simp only [Round3RepairFixedSmoothingPacket.mapDistance,hReferenceMap]
    rfl
  refine ⟨Fstar,(fun j => (run.state changed j).map),run.increment changed,run.stage changed,{
    initial := ?_
    maps_smooth := fun j => (run.state changed j).smooth
    increments_smooth := fun j => (run.full_increment_control changed he hDisp hTheta j).1
    actual_update := out.smooth_metric.full.actual_update
    stage_min := run.full_stage_ge_ten changed
    stage_step := out.smooth_metric.full.stage_step
    stages := out.smooth_metric.full.stages
    summable := out.smooth_metric.full.limit.1
    same_series := ?_
    joint_smooth := hFstar
    slice_smooth := fun p => hProduct.comp (contMDiff_const.prodMk contMDiff_id)
    exact_metric := out.smooth_metric.full.limit.2.2.1
    slice_immersion := fun p x => out.smooth_metric.immersion.immersion p (mem_univ _) x
    strict_C2 := ?_
    original_norms := out.smooth_metric.original_norms
    original_jets := out.smooth_metric.full.original_jets
    increment_bound := ?_
    original_phases := out.phases }⟩
  · rw [run.initial_state_map changed,hInitial,hReferenceMap]
  · rw [run.initial_state_map changed]
  · rw [← hNorm]
    exact (ENNReal.toReal_lt_toReal (out.smooth_metric.full.limit.2.2.2.2.1)
      ENNReal.ofReal_ne_top).mp (by simpa only [ENNReal.toReal_ofReal (he.le.trans hr)] using hBound)
  · intro j
    exact (run.full_increment_control changed he hDisp hTheta j).2.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hr (by norm_num))
        (iterationScale_pos ht0 j).le))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairCanonicalEnvelopeConstructedRepair.original_conclusion
