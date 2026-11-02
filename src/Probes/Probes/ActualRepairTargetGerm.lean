import Smoothing.TensorLocalPositive
import Smoothing.ParameterRound2TensorGermSpace
import Smoothing.ParameterRound2RepairRegularity

/-! The actual target SH-(deltaNext/delta)^2 gamma(F0) is an element of the
original symmetric tensor germ space. Symmetry comes from the actual signed
convolution and actual induced metric; it is not an output assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local instance actualRepairTargetChartedSpace : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
local instance actualRepairTargetIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem actual_repair_smoothed_target_germ_mem
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (G F0 : P × M → V) (hF0 : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ F0)
    (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hstarSymm : ∀ p x, (hstar p x).IsSymm)
    (mu : Measure (Ep × D)) (kernel : Ep × D → ℝ) (ell delta deltaNext : ℝ)
    (chi : Fin A.count × Fin c → P × M → ℝ) :
    let Hold := fun p x => (delta^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)) x)
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    (fun p x => SH p x-(deltaNext/delta)^2 • inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) ∈
      parameterRound2_originalTensorGermSpace A B.chart S W := by
  intro Hold SH hSH
  have hHsymm : ∀ z : P × M, (Hold z.1 z.2).IsSymm := by
    intro z
    exact ((hstarSymm z.1 z.2).sub (inducedMetric_isPosSemidef (I := 𝓙) (fun y => G (z.1,y)) z.2).isSymm).smul _
  have hSHsymm (p x) : (SH p x).IsSymm :=
    tensorFamilySmoothing_isSymm (parameterLocalProductFamily A B) mu kernel ell chi
      (tensorLocalParameterFrame A B hA) (fun z => Hold z.1 z.2) hHsymm (p,x)
  have hRef := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  constructor
  · intro i
    exact ⟨incrementsOriginalDifferentiation A B.chart i,
      parameterRound2_originalDifferentiation_open A B.chart i,hSO i,
      (hSH i).sub ((hRef i).const_smul ((deltaNext/delta)^2))⟩
  · intro z hz
    exact (hSHsymm z.1 z.2).sub ((inducedMetric_isPosSemidef (I := 𝓙)
      (fun y => F0 (z.1,y)) z.2).isSymm.smul _)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_smoothed_target_germ_mem
