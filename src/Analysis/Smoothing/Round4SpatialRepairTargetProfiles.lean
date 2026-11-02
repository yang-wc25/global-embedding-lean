import Smoothing.Round4SpatialClosedPairSameDomain
import Probes.ActualRepairTargetProfiles
import Probes.ActualRepairTargetGerm
import Smoothing.ParameterRound2LocalSetPair
import Smoothing.ParameterRound2RepairScales
import Smoothing.ParameterRound2OriginalFixedPacket

/-!
# Actual repair stage data from the finite raw-geometry smoother

The named pair constant is consumed here by the original smoothed map and
SH - (deltaNext/delta)^2 gamma(F0), in the original norm domains and germ
spaces. Both selected numerical profiles are the same explicit function of
raw geometry, so their j-th entries have the proved j+2 dependency. No new
smoothed-field derivative hypothesis or target entrance condition is added.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance round4SpatialRepairTargetChartedSpace : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance round4SpatialRepairTargetIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round4_actual_spatial_repair_target_slow_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let Cgain := fun j => round4SpatialPairConstant n d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    (∀ j, 0 ≤ Cgain j) ∧
    ∀ (c : ℕ) (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
      (RP : TensorLocalRawPreparation B univ BP0 TP0 Dp),
    radius ≤ min B.buffer A.buffer →
    ∀ (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) → (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    ∀ (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i),
    (∀ i, S i ⊆ incrementsOriginalEvaluation A B.chart Omega Q univ i) →
    ∀ ell t : ℝ, 0 < ell → ell ≤ t → t ≤ 1 →
    ∀ (G F0 : P × M → V),
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ G → ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ F0 →
    ∀ reference : ℕ → ℝ,
    (∀ j, (paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart
      (fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ reference j) →
    ∀ (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)),
    (∀ p x, (hstar p x).IsSymm) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart hstar i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    ∀ delta deltaNext : ℝ, (deltaNext/delta)^2 ≤ 1 →
    let Hold := fun p x => (delta^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)) x)
    ∀ budget : ℝ,
    (round4ParameterSpatialPairWeighted A B G Hold r t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius r
    let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    ∃ Target : parameterRound2_originalTensorGermSpace A B.chart S W,
      Target.val = (fun p x => SH p x-(deltaNext/delta)^2 • inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) ∧
      ∀ j, parameterRound2_originalTensorGermSeminorm A B.chart S W hS hSO ell j Target ≤
        Cgain j*budget+(j+1)*reference j := by
  have hs (j : ℕ) := round4_actual_spatial_closed_parameter_same_domain_pair
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cgain : ℕ → ℝ := fun j => round4SpatialPairConstant n d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
  have hCg (j) : 0 ≤ Cgain j := (hs j).1
  have hsmooth (j) := (hs j).2
  refine ⟨hCg,?_⟩
  intro c A B hA hB RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter
    S W hS hSO hSamples ell t hell helt ht1 G F0 hG hF0 reference hReference hstar hstarSymm hstarReg
    delta deltaNext ha1 Hold budget hbudget mu kernel chi SH
  let h0 := fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x
  let O := incrementsOriginalDifferentiation A B.chart
  have hO := parameterRound2_originalDifferentiation_open A B.chart
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB G hG
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn A B.chart hA hB G hG hstar hstarReg delta
  have hRef := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hj (j : ℕ) := hsmooth j c A B hA hB RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget
    hsource hparameter ell ell t hell le_rfl helt ht1 G hG Hold hHold budget hbudget
  have hSH := (hj 0).2.1
  have hHsymm : ∀ z : P × M, (Hold z.1 z.2).IsSymm := fun z =>
    ((hstarSymm z.1 z.2).sub (inducedMetric_isPosSemidef (I := 𝓙) (fun y => G (z.1,y)) z.2).isSymm).smul _
  let Smoothed : parameterRound2_originalTensorGermSpace A B.chart S W := ⟨SH,
    ⟨fun i => ⟨O i,hO i,hSO i,hSH i⟩,fun z hz =>
      tensorFamilySmoothing_isSymm (parameterLocalProductFamily A B) mu kernel ell chi
        (tensorLocalParameterFrame A B hA) (fun y => Hold y.1 y.2) hHsymm z⟩⟩
  let Ref : parameterRound2_originalTensorGermSpace A B.chart S W := ⟨h0,
    ⟨fun i => ⟨O i,hO i,hSO i,hRef i⟩,fun z hz => (inducedMetric_isPosSemidef (I := 𝓙) (fun y => F0 (z.1,y)) z.2).isSymm⟩⟩
  let a := (deltaNext/delta)^2
  let Target := Smoothed-a • Ref
  refine ⟨Target,rfl,?_⟩
  intro j
  let p := parameterRound2_originalTensorGermSeminorm A B.chart S W hS hSO ell j
  have hSl : paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B.chart SH) O S ≤
      round4ParameterSpatialPairWeighted A B
        (parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi G) SH j ell
        (incrementsOriginalEvaluation A B.chart Omega Q univ) :=
    (paperAtlasWeighted_mono_evaluation 0 j ell _ O S
      (incrementsOriginalEvaluation A B.chart Omega Q univ) hSamples).trans (le_add_left le_rfl)
  have hSb : p Smoothed ≤ Cgain j*budget :=
    (ENNReal.toReal_mono (hj j).2.2.2.2.1 hSl).trans (hj j).2.2.2.2.2
  have hRf := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalTensorCoordinates A B.chart h0) O S hO hS hSO hRef j
  have hRle := parameterRound2_paperAtlasWeighted_le_topOrder 0 j hell.le (helt.trans ht1)
    (incrementsOriginalTensorCoordinates A B.chart h0) O S
  have hRfin : (j+1 : ℝ≥0∞)*paperAtlasCj (j+0) (incrementsOriginalTensorCoordinates A B.chart h0) O S ≠ ⊤ :=
    ENNReal.mul_ne_top (by finiteness) (by simpa using hRf)
  have hRb : p Ref ≤ (j+1)*reference j := by
    have hh := ENNReal.toReal_mono hRfin hRle
    simp only [ENNReal.toReal_mul,ENNReal.toReal_add,ENNReal.toReal_natCast,ENNReal.toReal_one,Nat.add_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hReference j) (by positivity))
  have hnorm : p (a • Ref) ≤ p Ref := by
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (apply_nonneg _ _) ha1
  exact (map_sub_le_add p Smoothed (a • Ref)).trans (add_le_add hSb (hnorm.trans hRb))

#print axioms round4_actual_spatial_repair_target_slow_profiles
end GlobalEmbedding.Continuation
