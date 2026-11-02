import NormalPolar.FullResponseTail
import NormalPolar.NativeProbeValueTail

/-!
# The original native-Hessian input field from an actual C² correction

The same preliminary and final maps use the same original parameter ball,
threshold, fixed phases and normal values. The correction budget is literally
the native parameter derivative of their difference. This is the native input
to the proved same-Q response construction, with no identified-form premise.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

/-- The actual native-Hessian model modulus plus the original C² correction. -/
def nativeHessianTailModulus (n N : ℕ) (etaModel etaTail : ℝ → ℝ) (t : ℝ) : ℝ :=
  etaModel t + probeAtlasDerivativeConstant n N 2 * etaTail t

theorem nativeHessianTailModulus_nonneg (n N : ℕ) (etaModel etaTail : ℝ → ℝ)
    (hModel : ∀ t, 0 ≤ etaModel t) (hTail : ∀ t, 0 ≤ etaTail t) (t : ℝ) :
    0 ≤ nativeHessianTailModulus n N etaModel etaTail t :=
  add_nonneg (hModel t) (mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 2) (hTail t))

theorem nativeHessianTailModulus_tendsto (n N : ℕ) (etaModel etaTail : ℝ → ℝ)
    (hModel : Tendsto etaModel (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hTail : Tendsto etaTail (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (nativeHessianTailModulus n N etaModel etaTail) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  change Tendsto (fun t ↦ etaModel t + probeAtlasDerivativeConstant n N 2 * etaTail t)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero, add_zero] using
    hModel.add (hTail.const_mul (probeAtlasDerivativeConstant n N 2))

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- This conclusion is exactly the native_hessian_response field consumed by
NativeProbeData, including every original paired direction, chart support,
scale and parameter. The final map is F, with no change of its domain. -/
theorem nativeProbe_hessian_response_of_originalC2_correction
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {r : ℕ} (waves : Fin r → LocalLegalWave F₀ hF₀) (weight : Fin r → ℝ)
    (F G : ℝ → ProbeParameters r → M → V) (radius threshold : ℝ)
    (hF : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hG : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (G t)) (Metric.ball 0 radius ×ˢ univ))
    (etaModel etaTail : ℝ → ℝ) (CModel CTail C : ℝ)
    (hTail : ∀ t, 0 ≤ etaTail t) (hCTail : 0 ≤ CTail)
    (hC : CModel + probeAtlasDerivativeConstant n N 2 * CTail ≤ C)
    (hmodel : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b i x,
      x ∈ A.support i →
        ‖fderiv ℝ
            (fun v ↦ fderiv ℝ (fderiv ℝ (G t v ∘ (A.chart i).symm)) (A.chart i x))
            u (Pi.single (l, b) 1) -
          (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
            t ^ ((6 : ℝ) / 5))) •
            phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
              ((waves l).value ∘ (A.chart i).symm) (A.chart i x)‖ ≤
          t ^ ((44 : ℝ) / 5) * (etaModel t + CModel * ‖u‖))
    (htail : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b,
      probeAtlasCj A 2
        (fun y ↦ fderiv ℝ (fun v ↦ F t v y - G t v y) u (Pi.single (l, b) 1)) ≤
          ENNReal.ofReal (t ^ ((44 : ℝ) / 5) * (etaTail t + CTail * ‖u‖))) :
    ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b i x,
      x ∈ A.support i →
        ‖fderiv ℝ
            (fun v ↦ fderiv ℝ (fderiv ℝ (F t v ∘ (A.chart i).symm)) (A.chart i x))
            u (Pi.single (l, b) 1) -
          (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
            t ^ ((6 : ℝ) / 5))) •
            phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
              ((waves l).value ∘ (A.chart i).symm) (A.chart i x)‖ ≤
          t ^ ((44 : ℝ) / 5) * (nativeHessianTailModulus n N etaModel etaTail t + C * ‖u‖) := by
  intro t ht htt u hu l b i x hx
  have hu' : u ∈ Metric.ball (0 : ProbeParameters r) radius := by simpa using hu
  have htail' : probeAtlasCj A 2
      (fun y ↦ fderiv ℝ (fun v ↦ F t v y) u (Pi.single (l, b) 1) -
        fderiv ℝ (fun v ↦ G t v y) u (Pi.single (l, b) 1)) ≤
        ENNReal.ofReal (t ^ ((44 : ℝ) / 5) * (etaTail t + CTail * ‖u‖)) := by
    simpa only [actual_parameter_value_response_sub A hA hcover Metric.isOpen_ball
      (F t) (G t) (hF t ht htt) (hG t ht htt) u (Pi.single (l, b) 1) hu'] using
        htail t ht htt u hu l b
  have h := atlas_native_hessian_response_scaled_bound_of_originalC2_tail
    A hA i Metric.isOpen_ball (F t) (G t) (hF t ht htt) (hG t ht htt)
    u (Pi.single (l, b) 1) hu' x hx
    ((t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
      t ^ ((6 : ℝ) / 5))) •
      phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
        ((waves l).value ∘ (A.chart i).symm) (A.chart i x))
    (t ^ ((44 : ℝ) / 5)) (etaModel t) (etaTail t) CModel CTail
    (Real.rpow_nonneg ht.le _) (hTail t) hCTail (hmodel t ht htt u hu l b i x hx) htail'
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hC (norm_nonneg u))

end GlobalEmbedding.NormalPolar
