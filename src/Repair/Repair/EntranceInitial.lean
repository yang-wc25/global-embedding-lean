import Repair.EntranceNumeric
import Smoothing.Round3RepairInitialState

/-!
# The actual original repair entrance from one numerical reference class

The formulas for t0 and epsilon* are fixed before the reference map and
the target metric.  The literal map and its metric defect are constructed
here; neither an initial state nor an estimate for its output is assumed.
The only target entrance is the original C440 error.  All parameter
derivatives remain in the existing original full joint coordinate norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
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
private local instance : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- Uniform, explicit initialization of the same closed repair state.
`low` and `high` are numerical bounds fixed for the entire reference class;
there is no input-dependent choice of t0.  The target is only read after
both t0 and its error radius have been fixed by the displayed formulas. -/
theorem repairEntrance_uniform_initial_closed_state
    (budget epsilon eta cap low high : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap)
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hFixed : low+epsilon/4 ≤ budget/4)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hLow : round3RepairReferenceLowBase packet ≤ low)
    (hHigh :
      (paperAtlasCj 442 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal+
      (paperAtlasCj 440 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        Data.H) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ high) :
    let t0 := repairEntranceScale budget epsilon cap low high
    let targetRadius := repairEntranceMetricRadius t0 budget eta
    0 < t0 ∧ t0 ≤ (1/2 : ℝ) ∧ t0 ≤ cap ∧ 0 < targetRadius ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (fun p x => metric p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal targetRadius →
    ∃ initial : Round3RepairClosedState (packet.withMetric metric hSym hSmooth) budget epsilon eta 10 t0,
      initial.map=(fun z => Real.sqrt (1-t0^20) • packet.referenceMap z) ∧
      ∀ p x, (packet.withMetric metric hSym hSmooth).normalizedDefect initial.map 10 t0 p x =
        Data.H p x+(t0^20)⁻¹ • (metric p x-Data.H p x) := by
  classical
  intro t0 targetRadius
  have hbudget : 4*low < budget := by linarith
  have hbudget0 : 0 < budget := by linarith
  have ht0 : 0 < t0 := repairEntranceScale_pos hepsilon hcap hlow hhigh hbudget
  have htHalf : t0 ≤ (1/2 : ℝ) := repairEntranceScale_le_half budget epsilon cap low high
  have ht1 : t0 ≤ 1 := htHalf.trans (by norm_num)
  have hRadius : 0 < targetRadius := repairEntranceMetricRadius_pos ht0 hbudget0 heta
  refine ⟨ht0,htHalf,repairEntranceScale_le_cap budget epsilon cap low high,hRadius,?_⟩
  intro metric hSym hSmooth hError
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  let S := packet.closedSamples
  let h0 := fun p x => inducedMetric (I := IT) (fun y => packet.referenceMap (p,y)) x
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap
  let g := incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart h0
  let e := incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
    (fun p x => metric p x-h0 p x)
  have hO : ∀ i, IsOpen (O i) :=
    parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart
  have hS : ∀ i, IsCompact (S i) := packet.closedSamples_compact
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i) :=
    parameterRound2_inducedMetric_originalCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hf442 := parameterRound2_paperAtlasCj_finite_of_compact f O S hO hS hSO hf 442
  have hg440 := parameterRound2_paperAtlasCj_finite_of_compact g O S hO hS hSO hg 440
  have hLow' : (paperAtlasCj 2 f O S).toReal+(paperAtlasCj 0 g O S).toReal ≤ low := by
    unfold round3RepairReferenceLowBase at hLow
    rw [packet.reference_tensor] at hLow
    exact hLow
  have hHigh' : (paperAtlasCj 442 f O S).toReal+(paperAtlasCj 440 g O S).toReal ≤ high := by
    rw [packet.reference_tensor] at hHigh
    exact hHigh
  have href := repairEntrance_reference_pair_bound f g O S hf442 hg440 hlow hhigh
    hLow' hHigh' ht0.le (le_refl t0)
  have heBound : paperAtlasCj 440 e O S ≤ ENNReal.ofReal targetRadius := by
    rw [packet.reference_tensor] at hError
    exact hError
  have he440 : paperAtlasCj 440 e O S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heBound
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) := fun i => (hSmooth i).sub (hg i)
  let delta := t0^10
  have hdelta : 0 < delta := pow_pos ht0 _
  have hd2 : 0 < delta^2 := sq_pos_of_pos hdelta
  have hd2eq : delta^2=t0^20 := by dsimp only [delta]; rw [← pow_mul]
  have hdsmall : delta^2 ≤ 1 := pow_le_one₀ hdelta.le (pow_le_one₀ ht0.le ht1)
  have hinit := parameterRound2_initial_native_pair Data.atlas packet.parameterFamily
    packet.domain.atlas_smooth hB S hSO packet.referenceMap packet.referenceMap_smooth
    metric hSmooth 440 t0 delta ht0.le ht1 hdelta.ne' hdsmall hf442 hg440 he440
  dsimp only at hinit
  let G0 := fun z => Real.sqrt (1-delta^2) • packet.referenceMap z
  let changed := packet.withMetric metric hSym hSmooth
  have hmap : (changed.mapDistance G0).toReal ≤ (epsilon/4)*(1-t0) := by
    apply round3_repair_initial_scaling_C2_envelope Data.atlas packet.parameterFamily
      packet.domain.atlas_smooth hB S hS hSO packet.referenceMap packet.referenceMap_smooth
      hepsilon ht0.le htHalf
    have hF2 : (paperAtlasCj 2 f O S).toReal ≤ low := by
      linarith [ENNReal.toReal_nonneg (a := paperAtlasCj 0 g O S)]
    have htPaid : t0*(8*(low+1)) ≤ epsilon :=
      (le_div_iff₀ (by positivity : 0 < 8*(low+1))).mp
        (repairEntranceScale_le_scaling budget epsilon cap low high)
    apply (le_div_iff₀ (by positivity)).mpr
    change t0*(8*((paperAtlasCj 2 f O S).toReal+1)) ≤ epsilon
    nlinarith
  have heReal : (paperAtlasCj 440 e O S).toReal ≤ targetRadius := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top heBound
    simpa only [ENNReal.toReal_ofReal hRadius.le] using hh
  have hScale : (delta^2)⁻¹*441*targetRadius ≤ budget/4 := by
    have hr : targetRadius ≤ delta^2*(budget/(4*441)) := by
      dsimp only [targetRadius, repairEntranceMetricRadius]
      rw [hd2eq]
      exact min_le_left _ _
    calc
      _ ≤ (delta^2)⁻¹*441*(delta^2*(budget/(4*441))) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by field_simp
  have hPair : (changed.pairNorm G0 10 t0 440).toReal ≤ budget := by
    have hWf := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 440 t0 f O S hf442
    have hWg := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 440 t0 g O S hg440
    have hRefPair : (parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily
        packet.referenceMap h0 440 t0 S).toReal ≤ budget/2 := by
      change (paperAtlasWeighted 2 440 t0 f O S+paperAtlasWeighted 0 440 t0 g O S).toReal ≤ _
      rw [ENNReal.toReal_add hWf hWg]
      exact href
    have hb := hinit.2.2.2.2
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb
    have hErrorBudget := (mul_le_mul_of_nonneg_left heReal
      (by positivity : 0 ≤ (delta^2)⁻¹*441)).trans hScale
    change (changed.pairNorm G0 10 t0 440).toReal ≤ _ at hb
    linarith
  have hDefect : (changed.defectDistance G0 10 t0).toReal ≤ eta := by
    have hfieldEq : (fun p x => changed.normalizedDefect G0 10 t0 p x-Data.H p x) =
        fun p x => (delta^2)⁻¹ • (metric p x-h0 p x) := by
      funext p x
      rw [packet.reference_tensor]
      change (delta^2)⁻¹ • (metric p x-inducedMetric (I := IT) (fun y => G0 (p,y)) x)-h0 p x=_
      rw [hinit.1 p x]
      abel
    have heq : incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        (fun p x => changed.normalizedDefect G0 10 t0 p x-Data.H p x) =
          fun i y => (delta^2)⁻¹ • e i y := by rw [hfieldEq]; rfl
    have he0 := parameterRound2_paperAtlasCj_mono_order (show 0 ≤ 440 by omega) e O S
    have hes := parameterRound2_paperAtlasCj_smul_le 0 e O S hO hSO he
      (ne_top_of_le_ne_top he440 he0) ((delta^2)⁻¹)
    rw [abs_of_nonneg (inv_nonneg.mpr hd2.le)] at hes
    have hsmall : (delta^2)⁻¹*targetRadius ≤ eta/2 := by
      have hr : targetRadius ≤ delta^2*(eta/2) := by
        dsimp only [targetRadius,repairEntranceMetricRadius]
        rw [hd2eq]
        exact min_le_right _ _
      calc
        _ ≤ (delta^2)⁻¹*(delta^2*(eta/2)) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = _ := by field_simp
    have hEn : changed.defectDistance G0 10 t0 ≤ ENNReal.ofReal (eta/2) := by
      change paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        (fun p x => changed.normalizedDefect G0 10 t0 p x-Data.H p x)) O S ≤ _
      rw [heq]
      calc
        _ ≤ ENNReal.ofReal ((delta^2)⁻¹)*paperAtlasCj 0 e O S := hes
        _ ≤ ENNReal.ofReal ((delta^2)⁻¹)*ENNReal.ofReal targetRadius :=
          mul_le_mul_right (he0.trans heBound) _
        _ = ENNReal.ofReal ((delta^2)⁻¹*targetRadius) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hsmall
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEn
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ eta/2)] at hr
    linarith
  let initial : Round3RepairClosedState changed budget epsilon eta 10 t0 :=
    { map := G0, smooth := hinit.2.1, map_close := hmap, defect_close := hDefect, pair_budget := hPair }
  refine ⟨initial,?_,?_⟩
  · change (fun z => Real.sqrt (1-delta^2) • packet.referenceMap z)=_
    rw [hd2eq]
  · intro p x
    rw [packet.reference_tensor]
    change (delta^2)⁻¹ • (metric p x-inducedMetric (I := IT) (fun y => G0 (p,y)) x) =
      h0 p x+(t0^20)⁻¹ • (metric p x-h0 p x)
    rw [← hd2eq]
    exact hinit.1 p x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_initial_closed_state
