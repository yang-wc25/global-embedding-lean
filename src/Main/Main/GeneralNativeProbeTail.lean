import Main.GeneralLegalWaveAtlasFields
import NormalPolar.FullResponseTailField
import NormalPolar.NativeProbeValueResponse

/-!
# General-cutoff model responses plus the same actual repair tail

The common original parameter ball, native derivatives, original atlas
samples and complete correction difference are retained. The old generic
Hessian and value correction inequalities apply to the literal arbitrary
phase and cutoff-normal values. No radial bump property is used.
-/
noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
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
theorem generalNativeProbe_hessian_response_of_originalC2_correction
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) (weight : Fin r → ℝ)
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

/-- The exact original value-response inequality for the final actual map.
The whole original parameter ball and scale interval are retained. The common
constant can be selected by the upstream construction before using this lemma;
only the displayed numerical comparison is required. -/
theorem generalNativeProbe_value_response_of_originalC0_correction
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) (weight : Fin r → ℝ)
    (F G : ℝ → ProbeParameters r → M → V) (radius threshold : ℝ)
    (hF : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hG : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (G t)) (Metric.ball 0 radius ×ˢ univ))
    (etaModel etaTail : ℝ → ℝ) (CModel CTail C : ℝ)
    (hTail : ∀ t, 0 ≤ etaTail t) (hCTail : 0 ≤ CTail)
    (hC : CModel + nativeValueTailConstant N * CTail ≤ C)
    (hmodel : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b x,
      ‖fderiv ℝ (fun v ↦ G t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤ t ^ ((56 : ℝ) / 5) * (etaModel t + CModel * ‖u‖))
    (htail : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b,
      probeAtlasCj A 0
        (fun y ↦ fderiv ℝ (fun v ↦ F t v y - G t v y) u (Pi.single (l, b) 1)) ≤
          ENNReal.ofReal (t ^ ((56 : ℝ) / 5) * (etaTail t + CTail * ‖u‖))) :
    ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b x,
      ‖fderiv ℝ (fun v ↦ F t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤ t ^ ((56 : ℝ) / 5) *
            (nativeValueTailModulus N etaModel etaTail t + C * ‖u‖) := by
  intro t ht htt u hu l b x
  have hu' : u ∈ Metric.ball (0 : ProbeParameters r) radius := by simpa using hu
  have h := actual_value_response_scaled_bound_of_originalCj_correction A hA hcover 0
    Metric.isOpen_ball (F t) (G t) (hF t ht htt) (hG t ht htt)
    u (Pi.single (l, b) 1) hu' x
    ((-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
      probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) • (waves l).value x)
    (t ^ ((56 : ℝ) / 5)) (etaModel t) (etaTail t) CModel CTail
    (Real.rpow_nonneg ht.le _) (hTail t) hCTail
    (hmodel t ht htt u hu l b x) (htail t ht htt u hu l b)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hC (norm_nonneg u))


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.generalNativeProbe_hessian_response_of_originalC2_correction
#print axioms GlobalEmbedding.Continuation.generalNativeProbe_value_response_of_originalC0_correction
