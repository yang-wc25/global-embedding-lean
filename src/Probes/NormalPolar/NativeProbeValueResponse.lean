import NormalPolar.NativeProbeValueTail

/-!
# The original paired value-response field from a genuine correction budget

The source is one preliminary actual map and the final actual map on the same
parameter domain. The leading phase, normal value, paired direction and weight
are identical. The derivative of their genuine difference is controlled in
the original atlas C⁰ norm. This supplies precisely NativeProbeData's value
response; neither map, its correction, nor its raw estimates are constructed
here.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The exact original value-response inequality for the final actual map.
The whole original parameter ball and scale interval are retained. The common
constant can be selected by the upstream construction before using this lemma;
only the displayed numerical comparison is required. -/
theorem nativeProbe_value_response_of_originalC0_correction
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

end GlobalEmbedding.NormalPolar
