import Probes.ActualRepairTargetProfiles
import Smoothing.ParameterRound2OriginalFixedPacket

/-! The SAME signed-kernel smoother supplies the actual original stage
background, target, and every original given-input profile. The only packet
budget left outside the smoother is the actual given cutoff/normal/linear,
phase differential and original chart-transition data at fixed scale one.
No smoothed-map or smoothed-target derivative estimate is assumed. -/
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
local instance actualOriginalSmoothedStageChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance actualOriginalSmoothedStageIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem exists_uniform_parameterRound2_original_smoothed_stage_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ Cmap : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧ ∀
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
    (∀ i, S i ⊆ tensorLocalOriginalInner Data.atlas B Data.parameterSet i) →
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
  have hm (j : ℕ) := exists_uniform_parameterRound2_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cmap : ℕ → ℝ := fun j => Classical.choose (hm j)
  have hCmap : ∀ j, 0 ≤ Cmap j := fun j => (Classical.choose_spec (hm j)).1
  obtain ⟨Ctarget,hCtarget,htarget⟩ := exists_uniform_actual_repair_target_slow_profiles
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,?_⟩
  intro Data B hchart hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    S hS hSinner ell t hell helt ht1 G F0 hG hF0 reference hReference hstar hstarSymm hstarReg
    delta deltaNext ha1 Hold budget hbudget mu kernel chi SF SH hDataF hDataH givenPacket hFixedFin hFixed W O
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas B.chart i := by
    intro i y hy
    simpa only [hchart] using hy.1
  have htarg := htarget Data.parameterCount Data.atlas B hA hB Data.parameterSet RS RP hbuffer
    Omega Q hOmega hQ hOT hQT hsource hparameter S W hS hSO hSinner ell t hell helt ht1 G F0 hG hF0
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
  have hpair := (Classical.choose_spec (hm j)).2 Data.parameterCount Data.atlas B hA hB Data.parameterSet
    RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter S hSinner ell ell t hell le_rfl helt ht1
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

#print axioms exists_uniform_parameterRound2_original_smoothed_stage_profiles
end GlobalEmbedding.Continuation
