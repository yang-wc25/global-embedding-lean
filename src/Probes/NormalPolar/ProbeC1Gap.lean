import NormalPolar.ActualMapC1Gap
import NormalPolar.PositivePresentationGlobalGap
import NormalPolar.NativeProbeConstruction

/-!
# Original probe certificates from genuine spatial C¹ displacement

These attach a sharper zero-order modulus to the identical probe and Q.
The additional input is only an actual spatial C¹ displacement estimate.
In particular a t^10 modulus cannot be inferred merely from parameter_C1:
the original interface does not assume that the parameter-zero slice is F₀.
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

/-- The original positively presented probe keeps its literal Q and full
response. Its actual spatial C¹ displacement supplies the zero-order gap. -/
def chosenProbeNormalGapOfPositivePresentationC1
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hlim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
      probeAtlasCj A 1 (p.map t u - F₀) ≤ ENNReal.ofReal (b t)) :
    ChosenProbeNormalGap p where
  gap := totalNormalLinearGap (nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀) b
  gap_nonneg := totalNormalLinearGap_nonneg _
    (nativeReferenceResponseFactor_pos A hA hcompact F₀ hF₀ hi₀).le b hb
  gap_tendsto := totalNormalLinearGap_tendsto _ b hlim
  gap_bound := by
    intro t ht htt u hu i x hx
    have hp := presentation.operator_gap_le_four t ht htt u hu x
    have hd := sameMetric_normalProjection_gap_originalC1 A hA hcompact hcover F₀ hF₀ hi₀
      (p.map t u) (p.slice_smooth t u) (p.metric t ht htt u hu)
      (b t) (hb t) (hbudget t ht htt u hu) x
    apply hp.trans
    simpa only [totalNormalLinearGap, mul_assoc] using
      mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4)

namespace NativeProbeData
variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- Any true spatial C¹ displacement modulus gives a certificate for the
same already constructed full original probe, without changing its response. -/
def chosenNormalGapOfC1 [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hlim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      probeAtlasCj A 1 (d.map t u - F₀) ≤ ENNReal.ofReal (b t)) :
    ChosenProbeNormalGap d.toExactProbeFamily where
  gap := totalNormalLinearGap (nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀) b
  gap_nonneg := totalNormalLinearGap_nonneg _
    (nativeReferenceResponseFactor_pos A hA hcompact F₀ hF₀ hi₀).le b hb
  gap_tendsto := totalNormalLinearGap_tendsto _ b hlim
  gap_bound := by
    intro t ht htt u hu i x hx
    exact actualImmersionNormalIdentification_gap_originalC1_linear A hA hcompact hcover
      F₀ hF₀ hi₀ (d.map t u) (d.slice_smooth t u) (d.immersion t u)
      (d.metric t ht htt u hu) (b t) (hb t) (hbudget t ht htt u hu) x

/-- A genuine t^10 spatial C¹ displacement, when supplied upstream, gives
that stronger same-Q rate. It is not inferred from the parameter response. -/
def chosenNormalGapOfC1Ten [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (C : ℝ) (hC : 0 ≤ C)
    (hbudget : ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      probeAtlasCj A 1 (d.map t u - F₀) ≤ ENNReal.ofReal (C * t ^ (10 : ℕ))) :
    ChosenProbeNormalGap d.toExactProbeFamily := by
  apply d.chosenNormalGapOfC1 (fun t ↦ C * |t| ^ (10 : ℕ))
    (fun t ↦ mul_nonneg hC (pow_nonneg (abs_nonneg t) _))
  · have hc : Continuous (fun t : ℝ ↦ C * |t| ^ (10 : ℕ)) :=
      continuous_const.mul (continuous_abs.pow 10)
    simpa using (hc.tendsto 0).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · intro t ht htt u hu
    simpa only [abs_of_pos ht] using hbudget t ht htt u hu

@[simp] theorem chosenNormalGapOfC1Ten_gap [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (C : ℝ) (hC : 0 ≤ C)
    (hbudget : ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      probeAtlasCj A 1 (d.map t u - F₀) ≤ ENNReal.ofReal (C * t ^ (10 : ℕ))) :
    (d.chosenNormalGapOfC1Ten C hC hbudget).gap =
      fun t ↦ 4 * nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ *
        (C * |t| ^ (10 : ℕ)) := rfl

end NativeProbeData
end GlobalEmbedding.NormalPolar
