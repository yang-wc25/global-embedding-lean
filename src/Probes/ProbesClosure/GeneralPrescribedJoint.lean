import ProbesClosure.GeneralPhysicalResponses
import Main.OriginalPrescribedJoint

/-!
# Actual chart joint smoothness of the original prescribed family

Every subordinate piece already has joint smoothness from its own raw
construction. The finite sum uses the two original coordinates of each
label via a continuous linear projection. The actual physical family on
the unchanged original parameter ball agrees with that sum on whole
spatial slices, so it inherits the same joint smoothness there.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace GeneralLegalWaveRawFamily

/-- Grouping many actual pieces under one original label preserves global
parameter jointness without adding new independent parameter coordinates. -/
theorem originalPairMap_chart_joint
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × D =>
        family.originalPairMap c hc delta tau length z.1 ((A.chart i).symm z.2))
      (univ ×ˢ (A.chart i).target) := by
  exact originalProbePair_sum_joint (fun l => Fin (family.piece l).seed.refinement.count)
    (fun l s u y => family.piecePairMap c hc l s delta tau length u ((A.chart i).symm y))
    (A.chart i).target
    (fun l s => family.piecePairMap_chart_joint hImm hweight c hc l s delta tau length A hA i)

/-- Transfer across the proved literal grouped-map identity without
unfolding the large reconstructed map in the joint smoothness proof. -/
theorem groupedPairMap_chart_joint
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × D =>
        family.groupedPairMap c hc delta tau length z.1 ((A.chart i).symm z.2))
      (univ ×ˢ (A.chart i).target) := by
  apply (family.originalPairMap_chart_joint hImm hweight c hc delta tau length A hA i).congr
  intro z _
  exact congrFun (congrFun (family.groupedPairMap_eq_originalPairMap c hc delta tau length)
    z.1) ((A.chart i).symm z.2)

variable {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]

/-- Jointness of the same physical prescribed component used by the actual
initialized first map, on its entire original ball and each entire chart
target. No output smoothness certificate is required as an input. -/
theorem centeredPhysicalPairMap_chart_joint
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin (Fintype.card (Fin r × Bool))) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) (i : Fin A.count) :
    ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × D =>
        family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ z.1
          ((A.chart i).symm z.2))
      (Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) ×ˢ
        (A.chart i).target) := by
  apply (family.groupedPairMap_chart_joint hImm hweight c hc delta tau length A hA i).congr_mono
  · intro z hz
    exact family.physicalPairMap_centered_original_ball c hc delta tau length
      B amplitude ha hbuffer b p₀ hp₀ z.1
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz.1) ((A.chart i).symm z.2)
  · exact Set.prod_mono (subset_univ _) Subset.rfl

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.originalPairMap_chart_joint
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.groupedPairMap_chart_joint
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.centeredPhysicalPairMap_chart_joint
