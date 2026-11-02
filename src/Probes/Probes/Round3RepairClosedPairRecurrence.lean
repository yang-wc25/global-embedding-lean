import Probes.Round3ParameterClosedRepairBudget
import Probes.ActualRepairPairRecurrenceAlgebra
import Probes.ActualRepairSixTermClosure

/-! The actual general-parameter update satisfies the original full pair
recurrence on ONE fixed compact Ω/Q sampling domain.  The six tensor errors,
the actual cross term, and base-two displacement are supplied by the SAME U.
The next pair's domain is exactly the old convolution-budget domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)
local instance round3RepairClosedPairChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3RepairClosedPairIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

def round3RepairClosedTensorCost (Cs Cmap Cmetric : ℕ → ℝ) (j : ℕ) : ℝ :=
  Cmetric j+Cs j+actualRepairCrossCost (m+1) d N j*Cs j*Cmap j

def round3RepairClosedPairCost (Cs Cmap Cmetric : ℕ → ℝ) (j : ℕ) : ℝ :=
  round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric j+(j+1)*Cmap (j+1)

private theorem round3_repair_closed_tensor_scalar
    {t delta deltaNext tau ell budget inherited Cs Cu Cm Cx : ℝ} {q : ℕ}
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (htau : 0 < tau) (ht : 0 < t)
    (hB : 0 ≤ budget) (hI : 0 ≤ inherited)
    (hCs : 0 ≤ Cs) (hCu : 0 ≤ Cu) (hCm : 0 ≤ Cm) (hCx : 0 ≤ Cx) :
    (deltaNext^2)⁻¹*(Cm*(delta*(tau/ell)^q+delta^3/tau)+
      delta^2*(Cs*(budget*(ell/t)^q+inherited*(tau/t)^q))+
      Cx*(Cs*(budget*(ell/t)^q+inherited*(tau/t)^q))*(Cu*delta)) ≤
    (deltaNext^2)⁻¹*(Cm+Cs+Cx*Cs*Cu)*
      (delta*(tau/ell)^q+delta^3/tau+(delta^2+delta)*(budget*(ell/t)^q+inherited*(tau/t)^q)) := by
  let C := Cm+Cs+Cx*Cs*Cu
  let rate := delta*(tau/ell)^q+delta^3/tau
  let tail := budget*(ell/t)^q+inherited*(tau/t)^q
  have hRate : 0 ≤ rate := by dsimp only [rate]; positivity
  have hTail : 0 ≤ tail := by dsimp only [tail]; positivity
  have hTriple : 0 ≤ Cx*Cs*Cu := by positivity
  have h1 : Cm*rate ≤ C*rate := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hRate
  have h2 : delta^2*(Cs*tail) ≤ C*delta^2*tail := by
    have hle : Cs ≤ C := by dsimp only [C]; linarith
    nlinarith only [mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg delta) hTail)]
  have h3 : Cx*(Cs*tail)*(Cu*delta) ≤ C*delta*tail := by
    have hle : Cx*Cs*Cu ≤ C := by dsimp only [C]; linarith
    nlinarith only [mul_le_mul_of_nonneg_right hle (mul_nonneg hdelta hTail)]
  calc
    _ ≤ (deltaNext^2)⁻¹*(C*(rate+(delta^2+delta)*tail)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      nlinarith only [h1,h2,h3]
    _ = _ := by dsimp only [C,rate,tail]; ring

/-- Original (6.8) for the same global U, with literal paper scales and both
next-stage alternatives.  All old and new norms use the same Ω/Q domain. -/
theorem round3_repair_closed_full_pair_and_defect_recurrence
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (k : ℕ) (hk : 10 ≤ k) :
    ∃ Cs : ℕ → ℝ, (∀ j, 0 ≤ Cs j) ∧ ∀ (Cmap Cmetric : ℕ → ℝ),
    (∀ j, 0 ≤ Cmap j) → (∀ j, 0 ≤ Cmetric j) →
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    (∀ j, 0 ≤ Cpair j) ∧ ∀
      (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
      (RP : TensorLocalRawPreparation B univ BP0 TP0 Dp),
    radius ≤ min B.buffer A.buffer →
    ∀ (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
    (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ s : ℕ, s ≤ k+1 →
    ∀ (oldMap : P × M → V), ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ oldMap →
    ∀ (metric h0 : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart metric i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart h0 i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    let delta := t^k
    let tau := t^(6/5 : ℝ)
    let ell := t^(11/10 : ℝ)
    let deltaNext := tau^s
    let q := 40*(k+1)
    let Hold := fun p x => (delta^2)⁻¹ •
      (metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x)
    let S := incrementsOriginalEvaluation A B.chart Omega Q univ
    ∀ budget : ℝ, (parameterLocalOriginalTotalPairWeighted A B oldMap Hold q t S).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius q
    let chi := parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi oldMap
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    ∀ (U : P × M → V),
    Round3ParameterJointIncrementConclusion A B.chart S univ SF U
      (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) q delta tau ell Cmap Cmetric →
    let nextMap := fun z => oldMap z+U z
    let Hnext := fun p x => (deltaNext^2)⁻¹ •
      (metric p x-inducedMetric (I := IT) (fun y => nextMap (p,y)) x)
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ nextMap ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Hnext i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    (∀ p x, metric p x-inducedMetric (I := IT) (fun y => nextMap (p,y)) x = deltaNext^2 • Hnext p x) ∧
    ∀ j,
      let inherited := (parameterLocalOriginalTotalPairWeighted A B oldMap Hold j t S).toReal
      let nextPair := parameterLocalOriginalTotalPairWeighted A B nextMap Hnext j tau S
      (nextPair ≠ ⊤ ∧ nextPair.toReal ≤
        (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart oldMap)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+
        (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart h0)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+
        (1+j*(paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart h0)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+2*Cpair j*(1+budget))*
          t^(1/5 : ℝ)*(1+inherited)) ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B.chart
        (fun p x => Hnext p x-h0 p x)) (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
       (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B.chart
        (fun p x => Hnext p x-h0 p x)) (incrementsOriginalDifferentiation A B.chart) S).toReal ≤
         (2*round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric j*(1+budget))*
           t^(1/5 : ℝ)*(1+inherited)) := by
  obtain ⟨Cs,hCs,hTensor⟩ := round3Parameter_actual_closed_repair_tensor_budget
    (m := m) (d := d) (N := N) (c := c) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1))
  refine ⟨Cs,hCs,?_⟩
  intro Cmap Cmetric hCmap hCmetric Cpair
  have hCd (j : ℕ) : 0 ≤ round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric j := by
    exact add_nonneg (add_nonneg (hCmetric j) (hCs j))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N j) (hCs j)) (hCmap j))
  have hCu (j : ℕ) : 0 ≤ (j+1:ℝ)*Cmap (j+1) := mul_nonneg (by positivity) (hCmap (j+1))
  refine ⟨fun j => add_nonneg (hCd j) (hCu j),?_⟩
  intro A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSource hParameter t ht ht1 s hs
    oldMap hOld metric h0 hMetric hRef delta tau ell deltaNext q Hold S budget hBudget
    mu kernel chi SF SH U hout nextMap Hnext
  have hOrder := repair_step_scale_order ht ht1 k hk
  have htau : 0 < tau := Real.rpow_pos_of_pos ht _
  have hell : 0 < ell := Real.rpow_pos_of_pos ht _
  have hDelta : 0 < delta := pow_pos ht _
  have hNext : deltaNext ≠ 0 := (pow_pos htau _).ne'
  have hClosed := hTensor A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSource hParameter
    tau ell t htau hOrder.2.2.1 hOrder.2.2.2 ht1 oldMap hOld metric h0 hMetric delta deltaNext hDelta hNext
    budget hBudget U q Cmap Cmetric hCmap hout
  refine ⟨hClosed.1,hClosed.2.1,hClosed.2.2.1,?_⟩
  intro j inherited nextPair
  let O := incrementsOriginalDifferentiation A B.chart
  let f := incrementsOriginalMapCoordinates A B.chart oldMap
  let u := incrementsOriginalMapCoordinates A B.chart U
  let ref := incrementsOriginalTensorCoordinates A B.chart h0
  let defect := incrementsOriginalTensorCoordinates A B.chart (fun p x => Hnext p x-h0 p x)
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric j
  let Cu := (j+1:ℝ)*Cmap (j+1)
  let CE := 2*Cd*(1+budget)
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hBudget
  have hCE : 0 ≤ CE := mul_nonneg (mul_nonneg (by norm_num) (hCd j)) (by linarith)
  have hScalar := round3_repair_closed_tensor_scalar hDelta.le hell htau ht hbudget0
    (show 0 ≤ inherited from ENNReal.toReal_nonneg) (hCs j) (hCmap j) (hCmetric j)
    (actualRepairCrossCost_nonneg (m+1) d N j) (deltaNext := deltaNext) (q := q)
  have hScale := actual_repair_stage_scalar_bounds ht ht1 (hCd j) hbudget0
    (show 0 ≤ inherited from ENNReal.toReal_nonneg) k s hk hs rfl rfl rfl rfl rfl
  have hDefect := (hClosed.2.2.2 j).2.trans (hScalar.trans hScale.1)
  have hUbound := round3Parameter_same_increment_base_two_budget A B.chart S univ SF U
    (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) q delta tau ell htau Cmap Cmetric hout j
  have hOldCoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB oldMap hOld
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn A B.chart hA hB
    oldMap hOld metric hMetric delta
  have hFull := parameterRound2_original_pair_on_compact_finite A B Omega Q hOmega hQ hOT hQT
    oldMap hOldCoords Hold hHold j t
  have hOldLe : paperAtlasWeighted 2 j t f O S ≤ parameterLocalOriginalTotalPairWeighted A B oldMap Hold j t S :=
    le_add_right le_rfl
  have hOldFin := ne_top_of_le_ne_top hFull hOldLe
  have hS : ∀ i, IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact A B.chart Omega Q hOmega hQ hOT hQT
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hO := parameterRound2_originalDifferentiation_open A B.chart
  have hRefFinite := parameterRound2_paperAtlasCj_finite_of_compact ref O S hO hS hSO hRef j
  have hFG : ∀ i, ∃ V0, IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (f i) V0 :=
    fun i => ⟨O i,hO i,hSO i,hOldCoords i⟩
  have hUG : ∀ i, ∃ V0, IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (u i) V0 := by
    intro i
    obtain ⟨V0,hV0,hSV0,hVO,hreg⟩ := hout.map_germs i
    exact ⟨V0,hV0,hSV0,hreg⟩
  have hRG : ∀ i, ∃ V0, IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (ref i) V0 :=
    fun i => ⟨O i,hO i,hSO i,hRef i⟩
  have hDG : ∀ i, ∃ V0, IsOpen V0 ∧ S i ⊆ V0 ∧ ContDiffOn ℝ ∞ (defect i) V0 :=
    fun i => ⟨O i,hO i,hSO i,(hClosed.2.1 i).sub (hRef i)⟩
  have hp := actual_repair_pair_norm_from_components j tau t delta (t^(1/5 : ℝ)) Cu CE inherited
    htau ht (hOrder.2.2.1.trans hOrder.2.2.2) ht1 f u ref defect O S hO hSO hFG hUG hRG hDG
    hOldFin hRefFinite hUbound.1 (hClosed.2.2.2 j).1 (ENNReal.toReal_mono hFull hOldLe) hUbound.2 hDefect
  have heq : (fun i x => defect i x+ref i x) = incrementsOriginalTensorCoordinates A B.chart Hnext := by
    funext i x a
    change (incrementsOriginalTensorCoordinates A B.chart Hnext i x a-
      incrementsOriginalTensorCoordinates A B.chart h0 i x a)+
      incrementsOriginalTensorCoordinates A B.chart h0 i x a =
      incrementsOriginalTensorCoordinates A B.chart Hnext i x a
    exact sub_add_cancel _ _
  rw [heq] at hp
  have hAbsorb := actual_repair_pair_component_absorption ht ht1 (hCu j) hCE
    (show 0 ≤ inherited from ENNReal.toReal_nonneg)
    (show 0 ≤ (paperAtlasCj j ref O S).toReal from ENNReal.toReal_nonneg) j k hk
  have hCost := actual_repair_pair_cost_increase Cd Cu budget (paperAtlasCj j ref O S).toReal j (hCu j) hbudget0
  have hIncrease := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCost
    (Real.rpow_nonneg ht.le (1/5 : ℝ))) (show 0 ≤ 1+inherited by positivity)
  exact ⟨⟨hp.1,actual_repair_pair_finish hp.2 (hAbsorb.trans hIncrease)⟩,
    (hClosed.2.2.2 j).1,hDefect⟩

theorem round3_repair_closed_full_pair_recurrence
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (k : ℕ) (hk : 10 ≤ k) :
    ∃ Cs : ℕ → ℝ, (∀ j, 0 ≤ Cs j) ∧ ∀ (Cmap Cmetric : ℕ → ℝ),
    (∀ j, 0 ≤ Cmap j) → (∀ j, 0 ≤ Cmetric j) →
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    (∀ j, 0 ≤ Cpair j) ∧ ∀
      (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
      (RP : TensorLocalRawPreparation B univ BP0 TP0 Dp),
    radius ≤ min B.buffer A.buffer →
    ∀ (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
    (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ s : ℕ, s ≤ k+1 →
    ∀ (oldMap : P × M → V), ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ oldMap →
    ∀ (metric h0 : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart metric i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart h0 i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    let delta := t^k
    let tau := t^(6/5 : ℝ)
    let ell := t^(11/10 : ℝ)
    let deltaNext := tau^s
    let q := 40*(k+1)
    let Hold := fun p x => (delta^2)⁻¹ •
      (metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x)
    let S := incrementsOriginalEvaluation A B.chart Omega Q univ
    ∀ budget : ℝ, (parameterLocalOriginalTotalPairWeighted A B oldMap Hold q t S).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius q
    let chi := parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi oldMap
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    ∀ (U : P × M → V),
    Round3ParameterJointIncrementConclusion A B.chart S univ SF U
      (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) q delta tau ell Cmap Cmetric →
    let nextMap := fun z => oldMap z+U z
    let Hnext := fun p x => (deltaNext^2)⁻¹ •
      (metric p x-inducedMetric (I := IT) (fun y => nextMap (p,y)) x)
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ nextMap ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Hnext i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    (∀ p x, metric p x-inducedMetric (I := IT) (fun y => nextMap (p,y)) x = deltaNext^2 • Hnext p x) ∧
    ∀ j,
      let inherited := (parameterLocalOriginalTotalPairWeighted A B oldMap Hold j t S).toReal
      let nextPair := parameterLocalOriginalTotalPairWeighted A B nextMap Hnext j tau S
      nextPair ≠ ⊤ ∧ nextPair.toReal ≤
        (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart oldMap)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+
        (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart h0)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+
        (1+j*(paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart h0)
          (incrementsOriginalDifferentiation A B.chart) S).toReal+2*Cpair j*(1+budget))*
          t^(1/5 : ℝ)*(1+inherited) := by
  obtain ⟨Cs,hCs,hMain⟩ := round3_repair_closed_full_pair_and_defect_recurrence
    (m := m) (d := d) (N := N) (c := c) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius k hk
  refine ⟨Cs,hCs,?_⟩
  intro Cmap Cmetric hCmap hCmetric Cpair
  have hUniform := hMain Cmap Cmetric hCmap hCmetric
  refine ⟨hUniform.1,?_⟩
  intro A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSource hParameter t ht ht1 s hs
    oldMap hOld metric h0 hMetric hRef delta tau ell deltaNext q Hold S budget hBudget
    mu kernel chi SF SH U hout nextMap Hnext
  have h := hUniform.2 A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSource hParameter
    t ht ht1 s hs oldMap hOld metric h0 hMetric hRef budget hBudget U hout
  exact ⟨h.1,h.2.1,h.2.2.1,fun j => (h.2.2.2 j).1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_closed_full_pair_recurrence

#print axioms GlobalEmbedding.Continuation.round3_repair_closed_full_pair_and_defect_recurrence
