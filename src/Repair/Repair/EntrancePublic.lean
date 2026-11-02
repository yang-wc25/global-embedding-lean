import Repair.EntranceUniformEndpoint

/-!
# Direct public conclusions of the actual repair trajectory

This file exposes the same physical map and the same natural-time sequence
manufactured by `repairEntrance_actual_uniform_constructed_repair_endpoint`.
The public theorem does not ask for an initial state, a trajectory, output
estimates, or a limiting map.  Its fixed-reference geometric assumptions
remain explicit; uniform production of those geometric inputs from the
paper's bounded class is a separate obligation.

All norms and coordinate domains below are the inherited original
`paperAtlasCj`, `incrementsOriginalDifferentiation`, and closed sampling
domains.  In particular, no pointwise convergence is substituted for
convergence in every original norm.
-/

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

/-- The explicit conclusions for one actual limit and one actual natural-time
trajectory.  The stage variable reaches every finite order, while the single
sequence converges in every original norm, with all joint parameter jets. -/
structure RepairOriginalLimitConclusion
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (tolerance t0 : ℝ) (Fstar : P × M → Ey)
    (G u : ℕ → P × M → Ey) (stage : ℕ → ℕ) : Prop where
  initial : G 0 = fun z => Real.sqrt (1-t0^20) • Ref.F z
  maps_smooth : ∀ j, ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ (G j)
  increments_smooth : ∀ j, ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ (u j)
  actual_update : ∀ j, G (j+1) = fun z => G j z+u j z
  stage_min : ∀ j, 10 ≤ stage j
  stage_step : ∀ j, stage (j+1) = stage j ∨ stage (j+1) = stage j+1
  stages : Tendsto stage atTop atTop
  summable : ∀ z, Summable (fun j => u j z)
  same_series : Fstar = fun z => G 0 z+∑' j, u j z
  joint_smooth : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ey) ∞ Fstar
  slice_smooth : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Fstar (p,x))
  exact_metric : ∀ p, inducedMetric (I := 𝓙) (fun x => Fstar (p,x)) = metric p
  slice_immersion : ∀ p x,
    Function.Injective (mfderiv 𝓙 𝓘(ℝ,Ey) (fun y => Fstar (p,y)) x)
  strict_C2 :
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun z => Fstar z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples < ENNReal.ofReal tolerance
  original_norms : ∀ a, Tendsto (fun j => paperAtlasCj a
    (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun z => Fstar z-G j z))
    (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
    smoothing.closedSamples) atTop (𝓝 0)
  original_jets : ∀ i a y,
    y ∈ incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i →
    Tendsto (fun j => iteratedFDeriv ℝ a
      (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart (G j) i) y)
      atTop (𝓝 (iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart Fstar i) y))
  increment_bound : ∀ j, paperAtlasCj (stage j/2)
    (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart (u j))
    (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
    smoothing.closedSamples ≤ ENNReal.ofReal ((tolerance/8)*iterationScale t0 j)
  original_phases :
    ∃ domain : Fin Ref.primaryCount → Set (P × M),
      (∀ nu, domain nu ⊆ Ref.primaryDomain nu) ∧
      (∀ nu, tsupport (Ref.cutoff nu) ⊆ domain nu) ∧
      let E : IncrementsOriginalNativeData (m+1) d N M P :=
        {Ref with F := Fstar, primaryDomain := domain}
      ∃ hdE : IncrementsOriginalDomainConditions E,
      ∃ hsE : IncrementsOriginalSmoothInputs E,
        IncrementsOriginalPhaseConditions E hdE hsE

/-- Projection to a directly usable original-domain statement.  The input
here is the preceding *constructed* proposition; the main theorem below
produces it internally from the original fixed-reference assumptions. -/
theorem RepairUniformConstructedRepair.original_conclusion
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (C2 C442 : ℝ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary)
    [Fintype Β] [Fintype SubSecondary] (Lprimary : ℕ) (tolerance : ℝ)
    (h : RepairUniformConstructedRepair Ref smoothing C2 C442 Β SubSecondary Lprimary tolerance) :
    ∃ t0 targetRadius : ℝ, 0 < t0 ∧ t0 < 1 ∧ 0 < targetRadius ∧
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
  rcases h.to_round3 Ref smoothing C2 C442 Β SubSecondary Lprimary tolerance with
    ⟨budget,epsilon,eta,hb,he,het,hr,cost,Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,
      t0,ht0,ht1,htEntry,targetRadius,hRadius,hFinish⟩
  refine ⟨t0,targetRadius,ht0,ht1,hRadius,?_⟩
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

/-- Actual fixed-reference repair with a direct original-domain conclusion.
The target radius and literal initial scale are chosen before the target
metric; only its original C440 error is required.  Every displayed map and
all parameter derivatives refer to one constructed natural-time trajectory. -/
theorem repairEntrance_actual_original_public
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (hNormSource : Ref.sourceNormDomain = smoothing.Omega)
    (hNormParameter : Ref.parameterNormDomain = smoothing.Q)
    (hAll : Ref.parameterSet = univ)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref smoothing.domain hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hsRef)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (tolerance : ℝ) (hTolerance : 0 < tolerance)
    (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C2)
    (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C442) :
    ∃ t0 targetRadius : ℝ, 0 < t0 ∧ t0 < 1 ∧ 0 < targetRadius ∧
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
  obtain ⟨packet,profiles,secondary,hRepair⟩ :=
    repairEntrance_actual_uniform_constructed_repair_endpoint Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear
      Lprimary hLocal hImmRef lower hEllRef rho hReserve tolerance hTolerance
      C2 C442 hC2 hC442 hMap2 hMap442
  exact hRepair.original_conclusion Ref smoothing hReferenceMap C2 C442 _ _ Lprimary tolerance

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.RepairUniformConstructedRepair.original_conclusion

#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_original_public
