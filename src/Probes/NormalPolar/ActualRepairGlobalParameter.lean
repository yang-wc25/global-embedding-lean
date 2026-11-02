import NormalPolar.ActualRepairParameterCutoff

/-!
# A globally smooth probe parameter with the unchanged local repair radius

The two cutoff radii are chosen strictly between the actual image of the
Pi-norm repair ball and the original chart buffer.  Thus the construction
works on a compact parameter manifold while agreeing with the full original
probe parameter on its entire previously selected ball.  Both coordinate
operator norms and the nonzero chart centre remain explicit.
-/

noncomputable section
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.NormalPolar

variable {d : ℕ} {ι P : Type*} [Fintype ι] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Fin d → ℝ

def actualRepairParameterBump (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P) :
    ContDiffBump (B.chart b p₀) where
  rIn := (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ + 1 / 3) *
    actualRepairParameterRadius B
  rOut := (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ + 2 / 3) *
    actualRepairParameterRadius B
  rIn_pos := mul_pos (by positivity) (actualRepairParameterRadius_pos B)
  rIn_lt_rOut := by
    have h := actualRepairParameterRadius_pos B
    nlinarith

theorem actualRepairParameterBump_outer_lt (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P) :
    (actualRepairParameterBump B b p₀).rOut < B.buffer := by
  let C := ‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hR := actualRepairParameterRadius_pos B
  have he : (C + 1) * actualRepairParameterRadius B = B.buffer := by
    dsimp only [actualRepairParameterRadius, C]
    field_simp
  change (C + 2 / 3) * actualRepairParameterRadius B < _
  nlinarith

theorem actualRepairParameterBump_target (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    Metric.closedBall (B.chart b p₀) (actualRepairParameterBump B b p₀).rOut ⊆ (B.chart b).target := by
  intro z hz
  apply tensorLocalSampling_subset_target B b
  apply mem_iUnion.mpr
  refine ⟨B.chart b p₀, mem_iUnion.mpr ⟨tensorLocalInner_mem B b hp₀, ?_⟩⟩
  exact hz.trans_lt (actualRepairParameterBump_outer_lt B b p₀)

def actualRepairGlobalParameter (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P) : P → X :=
  fun p => EuclideanSpace.equiv (Fin d) ℝ
    (actualParameterChartCutoff (B.chart b) (B.chart b p₀) (actualRepairParameterBump B b p₀) p)

theorem actualRepairGlobalParameter_smooth (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, X) ∞ (actualRepairGlobalParameter B b p₀) :=
  (EuclideanSpace.equiv (Fin d) ℝ).contDiff.contMDiff.comp
    (actualParameterChartCutoff_smooth (B.chart b) (hB b) (B.chart b p₀)
      (actualRepairParameterBump B b p₀) (actualRepairParameterBump_target B b p₀ hp₀))

theorem actualRepairGlobalParameter_norm_le (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ p : P) :
    ‖actualRepairGlobalParameter B b p₀ p‖ ≤
      ‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖ * B.buffer := by
  exact ((EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      ((actualParameterChartCutoff_norm_le (B.chart b) (B.chart b p₀)
        (actualRepairParameterBump B b p₀) p).trans (actualRepairParameterBump_outer_lt B b p₀).le)
      (norm_nonneg _))

theorem actualRepairGlobalParameter_local_identity (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) :
    actualRepairGlobalParameter B b p₀ (actualRepairParameterMap B b p₀ u) = u := by
  have hv : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm u‖ ≤
      (actualRepairParameterBump B b p₀).rIn := by
    apply ((EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.le_opNorm u).trans
    apply (mul_le_mul_of_nonneg_left hu.le (norm_nonneg _)).trans
    change _ ≤ (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ + 1 / 3) *
      actualRepairParameterRadius B
    exact mul_le_mul_of_nonneg_right (by linarith) (actualRepairParameterRadius_pos B).le
  unfold actualRepairGlobalParameter actualRepairParameterMap
  rw [actualParameterChartCutoff_coordinates (B.chart b) (B.chart b p₀)
    (actualRepairParameterBump B b p₀) (actualRepairParameterBump_target B b p₀ hp₀) _ hv]
  exact (EuclideanSpace.equiv (Fin d) ℝ).apply_symm_apply u

/-- Every joint-order derivative of the local parameter is the actual
derivative of the identity on the original full Pi-norm ball. -/
theorem actualRepairGlobalParameter_local_jets (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : X) (hu : ‖u‖ < actualRepairParameterRadius B) (k : ℕ) :
    iteratedFDeriv ℝ k (fun v => actualRepairGlobalParameter B b p₀
      (actualRepairParameterMap B b p₀ v)) u = iteratedFDeriv ℝ k (id : X → X) u := by
  have he : (fun v => actualRepairGlobalParameter B b p₀
      (actualRepairParameterMap B b p₀ v)) =ᶠ[𝓝 u] (id : X → X) := by
    have hm : u ∈ Metric.ball (0 : X) (actualRepairParameterRadius B) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    filter_upwards [Metric.isOpen_ball.mem_nhds hm] with v hv
    exact actualRepairGlobalParameter_local_identity B b p₀ hp₀ v
      (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_smooth
#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_norm_le
#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_local_identity
#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_local_jets
