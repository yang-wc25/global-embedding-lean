import Smoothing.Round4ClosedPairFiniteGeometry
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
local instance round4RepairTargetChartedSpace : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
local instance round4RepairTargetIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round4_actual_repair_target_slow_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let Cgain := fun j => round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    (∀ j, 0 ≤ Cgain j) ∧
    ∀ (c : ℕ) (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (parameterSet : Set P) (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
      (RP : TensorLocalRawPreparation B parameterSet BP0 TP0 Dp),
    radius ≤ min B.buffer A.buffer →
    ∀ (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) → (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    ∀ (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i),
    (∀ i, S i ⊆ round3OuterOriginalEvaluation A B parameterSet i) →
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
    (parameterLocalOriginalTotalPairWeighted A B G Hold r t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius r
    let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    ∃ Target : parameterRound2_originalTensorGermSpace A B.chart S W,
      Target.val = (fun p x => SH p x-(deltaNext/delta)^2 • inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) ∧
      ∀ j, parameterRound2_originalTensorGermSeminorm A B.chart S W hS hSO ell j Target ≤
        Cgain j*budget+(j+1)*reference j := by
  have hs (j : ℕ) := round4_actual_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cgain : ℕ → ℝ := fun j => round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
  have hCg (j) : 0 ≤ Cgain j := (hs j).1
  have hsmooth (j) := (hs j).2
  refine ⟨hCg,?_⟩
  intro c A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter
    S W hS hSO hSouter ell t hell helt ht1 G F0 hG hF0 reference hReference hstar hstarSymm hstarReg
    delta deltaNext ha1 Hold budget hbudget mu kernel chi SH
  let h0 := fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x
  let O := incrementsOriginalDifferentiation A B.chart
  have hO := parameterRound2_originalDifferentiation_open A B.chart
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB G hG
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn A B.chart hA hB G hG hstar hstarReg delta
  have hRef := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hj (j : ℕ) := hsmooth j c A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget
    hsource hparameter S hSouter ell ell t hell le_rfl helt ht1 G hGcoords Hold hHold budget hbudget
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
      parameterLocalOriginalTotalPairWeighted A B
        (parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi G) SH j ell S := le_add_left le_rfl
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


theorem round4_actual_original_smoothed_stage_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let Cmap := fun j => round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧ ∀
    (Data : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hchart : B.chart = Data.parameterChart)
    (hA : IsSmoothBufferedAtlas Data.atlas)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (RS : TensorRawCutoffPreparation Data.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP0 TP0 Dp),
    radius ≤ min B.buffer Data.atlas.buffer → ∀
    (Omega : Fin Data.atlas.count → Set D) (Q : Fin Data.parameterCount → Set Ep),
    (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
    (∀ i, Omega i ⊆ (Data.atlas.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
    (∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Omega i) →
    (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    ∀ hS : ∀ i, IsCompact (S i),
    ∀ ell t : ℝ, 0 < ell → ell ≤ t → t ≤ 1 → ∀ (G F0 : P × M → V),
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ G →
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ F0 →
    ∀ reference : ℕ → ℝ,
    (∀ j, (paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas B.chart
      (fun p x => inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation Data.atlas B.chart) S).toReal ≤ reference j) →
    ∀ (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)),
    (∀ p x, (hstar p x).IsSymm) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas B.chart hstar i)
      (incrementsOriginalDifferentiation Data.atlas B.chart i)) →
    ∀ delta deltaNext : ℝ, (deltaNext/delta)^2 ≤ 1 →
    let Hold := fun p x => (delta^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)) x)
    ∀ budget : ℝ,
    (parameterLocalOriginalTotalPairWeighted Data.atlas B G Hold r t
      (incrementsOriginalEvaluation Data.atlas B.chart Omega Q univ)).toReal ≤ budget →
    let mu := (volume : Measure (Ep × D))
    let kernel := fixedSmoothingKernel mu radius hradius r
    let chi := parameterLocalProductCutoff Data.atlas B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily Data.atlas B) mu kernel ell chi G
    let SH := tensorLocalParameterSmoothing Data.atlas B hA mu kernel ell chi Hold
    Data.F = SF →
    Data.H = (fun p x => SH p x-(deltaNext/delta)^2 • inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) →
    ∀ givenPacket : ℕ → ℝ,
    (∀ j, parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤) →
    (∀ j, (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ givenPacket j) →
    let W := incrementsOriginalParameterRegion Data
    let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart
    ∃ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W,
    H.val = Data.H ∧
    (∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W hS
      (fun _ _ hy => hy.1) ell j H ≤ Ctarget j*budget+(j+1)*reference j) ∧
    (∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        max (Cmap j*budget) (max (Ctarget j*budget+(j+1)*reference j) (givenPacket j))) := by
  have hm (j : ℕ) := round4_actual_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cmap : ℕ → ℝ := fun j => round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
  let Ctarget := Cmap
  have hCmap : ∀ j, 0 ≤ Cmap j := fun j => (hm j).1
  obtain ⟨hCtarget,htarget⟩ := round4_actual_repair_target_slow_profiles
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨hCmap,hCtarget,?_⟩
  intro Data B hchart hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    S hS ell t hell helt ht1 G F0 hG hF0 reference hReference hstar hstarSymm hstarReg
    delta deltaNext ha1 Hold budget hbudget mu kernel chi SF SH hDataF hDataH givenPacket hFixedFin hFixed W O
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas B.chart i := by
    intro i y hy
    simpa only [hchart] using hy.1
  have hSouter : ∀ i, S i ⊆ round3OuterOriginalEvaluation Data.atlas B Data.parameterSet i := by
    intro i y hy
    refine ⟨hSO i hy, ?_⟩
    change (incrementsOriginalJointPoint Data.atlas B.chart i y).1 ∈ Data.parameterSet
    simpa only [hchart] using hy.2.2.2
  have htarg := htarget Data.parameterCount Data.atlas B hA hB Data.parameterSet RS RP hbuffer
    Omega Q hOmega hQ hOT hQT hsource hparameter S W hS hSO hSouter ell t hell helt ht1 G F0 hG hF0
    reference hReference hstar hstarSymm hstarReg delta deltaNext ha1 budget hbudget
  obtain ⟨H0,hH0,hHbudget0⟩ := htarg
  let H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W :=
    ⟨H0.val,by rw [← hchart]; exact H0.property⟩
  have hHData : H.val = Data.H := hH0.trans hDataH.symm
  have hHbudget : ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W hS
      (fun _ _ hy => hy.1) ell j H ≤ Ctarget j*budget+(j+1)*reference j := by
    intro j
    change (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart H0.val)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ _
    rw [← hchart]
    exact hHbudget0 j
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas B.chart hA hB G hG
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas B.chart hA hB
    G hG hstar hstarReg delta
  refine ⟨H,hHData,hHbudget,?_⟩
  intro j
  have hpair := (hm j).2 Data.parameterCount Data.atlas B hA hB Data.parameterSet
    RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter S hSouter ell ell t hell le_rfl helt ht1
    G hGcoords Hold hHold budget hbudget
  have hmle : paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates Data.atlas B.chart SF)
      (incrementsOriginalDifferentiation Data.atlas B.chart) S ≤
      parameterLocalOriginalTotalPairWeighted Data.atlas B SF SH j ell S := le_add_right le_rfl
  have hmfin := ne_top_of_le_ne_top hpair.2.2.2.2.1 hmle
  have hmbound := (ENNReal.toReal_mono hpair.2.2.2.2.1 hmle).trans hpair.2.2.2.2.2
  have htfin := parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W
    hS (fun _ _ hy => hy.1) H 0 j ell
  have htbound := hHbudget j
  change (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart H.val)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ _ at htbound
  rw [hHData] at htfin htbound
  rw [hchart,← hDataF] at hmfin hmbound
  exact parameterRound2_originalGivenProfile_of_same_scale_map_tensor Data j ell
    (Cmap j*budget) (Ctarget j*budget+(j+1)*reference j) (givenPacket j)
    hmfin hmbound htfin htbound (hFixedFin j) (hFixed j)


#print axioms round4_actual_repair_target_slow_profiles
#print axioms round4_actual_original_smoothed_stage_profiles
end GlobalEmbedding.Continuation
