import NormalPolar.NativeProbeTotalizationModel
import NormalPolar.ParameterDisplacementCenter

/-!
# Actual center defects for domain-only native input

The center used below is the genuine raw final map, not its model and not
the reference immersion. Its budget is transported through the proved
reference extension, then the actual parameter C1 estimate gives the sharper
same-Q gap for exactly the constructed original probe record.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}


/-- Actual raw center data suffice for the stronger gap on the final
constructed full probe. No outside slice property is required. -/
def NativeProbeDomainData.chosenNormalGapOfCenterTen [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily := by
  refine NativeProbeData.chosenNormalGapOfCenterTen d.toNativeProbeData Ccenter hCcenter ?_
  intro t ht htt
  have hzero : ‖(0 : ProbeParameters r)‖ < d.radius := by simpa using d.radius_pos
  have heq : d.toNativeProbeData.map t 0 = d.map t 0 := d.totalMap_eq t ht htt 0 hzero
  rw [heq]
  exact hcenter t ht htt

/-- The modulus explicitly includes the raw center defect and the original
parameter-radius contribution; both belong to the same actual final family. -/
@[simp] theorem NativeProbeDomainData.chosenNormalGapOfCenterTen_gap [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    (d.chosenNormalGapOfCenterTen Ccenter hCcenter hcenter).gap =
      fun t ↦ 4 * nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ *
        ((Ccenter + probeParameterDisplacementConstant n N * d.constant * d.radius) *
          |t| ^ (10 : ℕ)) := rfl

/-- The model route uses the actual repaired center, never a model-center
identity to erase an unproved repair defect. -/
def NativeProbeDomainModelData.chosenNormalGapOfCenterTen [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.toDomainData.chosenNormalGapOfCenterTen Ccenter hCcenter hcenter

/-- The same raw final center with its actual order-twelve repair budget
gives the rate without shrinking its original scale interval. -/
def NativeProbeDomainData.chosenNormalGapOfCenterTwelve [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.chosenNormalGapOfCenterTen (Ccenter * (max 1 d.threshold) ^ (2 : ℕ))
    (mul_nonneg hCcenter (sq_nonneg _))
    (originalC1_center_ten_of_twelve A F₀ d.map d.threshold Ccenter hCcenter hcenter)

/-- This model-route input is the actual repaired center defect. The
initial model is not identified with F₀ without proof. -/
def NativeProbeDomainModelData.chosenNormalGapOfCenterTwelve [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.toDomainData.chosenNormalGapOfCenterTwelve Ccenter hCcenter hcenter

end GlobalEmbedding.NormalPolar
