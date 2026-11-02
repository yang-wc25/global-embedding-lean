import Probes.Round3ParameterJointConclusion
import Smoothing.Round3OuterClosedPair
import Probes.ActualRepairIncrementConsumer
import Probes.ActualRepairWeightedRecurrence
import Smoothing.ParameterRound2RepairRegularity

/-! Actual closed-parameter repair on ONE fixed original compact sampling
norm. The SAME U supplies its second-order map budget, the metric remainder,
the true Cross(old−SF,U), the next normalized tensor, and global joint
regularity. The old high norm is retained on precisely the same Ω/Q domain;
no larger-domain budget or shrinking parameter intersection is inferred. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local instance round3ParameterClosedRepairChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3ParameterClosedRepairIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round3Parameter_same_increment_base_two_budget
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (q : ℕ) (delta tau ell : ℝ) (htau : 0 < tau) (Cmap Cmetric : ℕ → ℝ)
    (hout : Round3ParameterJointIncrementConclusion A B S W F U H q delta tau ell Cmap Cmetric)
    (j : ℕ) :
    paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ (j+1)*Cmap (j+1)*delta/tau := by
  have hu := hout.map0 (j+1)
  have hshift := actual_paper_weighted_base_shift 2 j htau
    (incrementsOriginalMapCoordinates A B U) (incrementsOriginalDifferentiation A B) S
    (by simpa only [Nat.add_assoc] using hu.1)
  refine ⟨hshift.1,hshift.2.trans ?_⟩
  calc
    _ ≤ (j+1)*(Cmap (j+1)*delta*tau)/tau^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [Nat.add_assoc] using hu.2) (by positivity)) (sq_nonneg _)
    _ = _ := by field_simp

theorem round3Parameter_actual_closed_repair_tensor_budget
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ Cs : ℕ → ℝ, (∀ j, 0 ≤ Cs j) ∧ ∀
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
    ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
    ∀ (oldMap : P × M → V), ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ oldMap →
    ∀ (metric h0 : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart metric i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    ∀ delta deltaNext : ℝ, 0 < delta → deltaNext ≠ 0 →
    let Hold := fun p x => (delta^2)⁻¹ •
      (metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x)
    let S := incrementsOriginalEvaluation A B.chart Omega Q univ
    ∀ budget : ℝ, (parameterLocalOriginalTotalPairWeighted A B oldMap Hold r t S).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius r
    let chi := parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi oldMap
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    ∀ (U : P × M → V) (q : ℕ) (Cmap Cmetric : ℕ → ℝ), (∀ j, 0 ≤ Cmap j) →
    Round3ParameterJointIncrementConclusion A B.chart S univ SF U
      (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) q delta tau ell Cmap Cmetric →
    let nextMap := fun z => oldMap z+U z
    let Hnext := fun p x => (deltaNext^2)⁻¹ •
      (metric p x-inducedMetric (I := 𝓙) (fun y => nextMap (p,y)) x)
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ nextMap ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Hnext i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    (∀ p x, metric p x-inducedMetric (I := 𝓙) (fun y => nextMap (p,y)) x = deltaNext^2 • Hnext p x) ∧
    ∀ j,
      let high := (parameterLocalOriginalTotalPairWeighted A B oldMap Hold j t S).toReal
      let tail := Cs j*(budget*(ell/t)^r+high*(tau/t)^r)
      let nextNorm := paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates A B.chart (fun p x => Hnext p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart) S
      nextNorm ≠ ⊤ ∧ nextNorm.toReal ≤ (deltaNext^2)⁻¹ *
        (Cmetric j*(delta*(tau/ell)^q+delta^3/tau)+delta^2*tail+
          actualRepairCrossCost (m+1) d N j*tail*(Cmap j*delta)) := by
  have hs (j : ℕ) := round3Outer_exists_uniform_closed_parameter_same_domain_pair
    (n := m+1) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  choose Cs hCs hSmooth using hs
  refine ⟨Cs,hCs,?_⟩
  intro A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSampling hParameter
    tau ell t htau htaul helt ht1 oldMap hOld metric h0 hMetric delta deltaNext hdelta hNext
    Hold S budget hBudget mu kernel chi SF SH U q Cmap Cmetric hCmap hout nextMap Hnext
  have hOldCoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB oldMap hOld
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn A B.chart hA hB oldMap hOld
    metric hMetric delta
  have hp (j : ℕ) := hSmooth j c A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hSampling hParameter
    tau ell t htau htaul helt ht1 oldMap hOldCoords Hold hHold budget hBudget
  have hSF : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ SF := (hp 0).1
  have hSFCoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB SF hSF
  have hU : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ U := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffOn_univ.mp hout.joint_smooth
  have hNextSmooth := parameterRound2_native_add_contMDiff oldMap U hOld hU
  refine ⟨hNextSmooth,parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
    A B.chart hA hB nextMap hNextSmooth metric hMetric deltaNext,?_,?_⟩
  · intro p x
    dsimp only [Hnext]
    rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hNext),one_smul]
  · intro j high tail nextNorm
    have hS : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
    have hPairFin := (hp j).2.2.1
    have hPairBound := (hp j).2.2.2.1
    have hMapLe : paperAtlasWeighted 2 j tau
        (incrementsOriginalMapCoordinates A B.chart (fun z => oldMap z-SF z))
        (incrementsOriginalDifferentiation A B.chart) S ≤
        parameterLocalOriginalTotalPairWeighted A B (fun z => oldMap z-SF z)
          (fun p x => Hold p x-SH p x) j tau S := le_add_right le_rfl
    have hTensorLe : paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates A B.chart (fun p x => Hold p x-SH p x))
        (incrementsOriginalDifferentiation A B.chart) S ≤
        parameterLocalOriginalTotalPairWeighted A B (fun z => oldMap z-SF z)
          (fun p x => Hold p x-SH p x) j tau S := le_add_left le_rfl
    have hMapFin := ne_top_of_le_ne_top hPairFin hMapLe
    have hTensorFin := ne_top_of_le_ne_top hPairFin hTensorLe
    have hMapBound := (ENNReal.toReal_mono hPairFin hMapLe).trans hPairBound
    have hTensorBound := (ENNReal.toReal_mono hPairFin hTensorLe).trans hPairBound
    have hTail : ∀ i, ∃ O, IsOpen O ∧ S i ⊆ O ∧ ContDiffOn ℝ ∞
        (incrementsOriginalTensorCoordinates A B.chart (fun p x => Hold p x-SH p x) i) O := by
      intro i
      exact ⟨incrementsOriginalDifferentiation A B.chart i,
        parameterRound2_originalDifferentiation_open A B.chart i,hS i,(hHold i).sub ((hp j).2.1 i)⟩
    have hh := actual_repair_germ_finite_increment_consumer A B.chart hA S hS oldMap SF U
      hOldCoords hSFCoords hout.map_germs metric h0 SH delta deltaNext tau hdelta.ne' hdelta.le hNext
      htau (htaul.trans (helt.trans ht1)) j (Cmetric j) (Cmap j)
      (delta*(tau/ell)^q+delta^3/tau) (hCmap j) hTail hout.metric_germ.1
      hTensorFin hMapFin (hout.metric j).1 (hout.metric j).2 (hout.map1 j).1 (hout.map1 j).2
    refine ⟨hh.2.1,hh.2.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
    have ht := mul_le_mul_of_nonneg_left hTensorBound (sq_nonneg delta)
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMapBound (actualRepairCrossCost_nonneg (m+1) d N j))
      (mul_nonneg (hCmap j) hdelta.le)
    linarith only [ht,hm]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_same_increment_base_two_budget
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_closed_repair_tensor_budget
