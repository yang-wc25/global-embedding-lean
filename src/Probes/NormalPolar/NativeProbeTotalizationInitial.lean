import NormalPolar.NativeProbeTotalizationCenter
import NormalPolar.ParameterDisplacementInitial

/-!
# The same actual normal identification from the genuine first map

The final center is derived from the source construction, not assumed:
G0 = sqrt(1-t^20) F0, G1 = G0 + U0, then the literal correction Fstar-G1.
The identity of the supplied actual initial map with G1 is an explicit input.
The full U0 is retained, including its generally nonzero background at u=0.

The resulting order-ten gap belongs to the same exact probe and the same
polar Q already constructed from the domain-only native analytic data.
This does not assert existence of those data or of the actual initial map.
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

/-- The coefficient of the actual center after absorption on the entire
original scale interval. It is fixed before the scale and parameter. -/
def actualProbeCenterC1Constant (threshold Cref Cinc Ctail : ℝ) : ℝ :=
  Cref * (max 1 threshold) ^ (10 : ℕ) + Cinc +
    Ctail * (max 1 threshold) ^ (2 : ℕ)

theorem actualProbeCenterC1Constant_nonneg
    (threshold : ℝ) {Cref Cinc Ctail : ℝ}
    (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail) :
    0 ≤ actualProbeCenterC1Constant threshold Cref Cinc Ctail := by
  have hR : 0 ≤ max 1 threshold := le_trans zero_le_one (le_max_left _ _)
  exact add_nonneg (add_nonneg (mul_nonneg hCref (pow_nonneg hR _)) hCinc)
    (mul_nonneg hCtail (pow_nonneg hR _))

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- Prove the real raw center bound from the full initial increment and the
same initial map appearing in the actual repair tail. The identity obligation
is deliberately visible until the upstream closed-state producer supplies it. -/
theorem NativeProbeDomainData.actual_center_originalC1_of_initial
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (initial U₀ : ℝ → ProbeParameters r → M → V)
    (hidentity : ∀ t, 0 < t → t < d.threshold →
      initial t 0 = actualProbeFirstMap F₀ U₀ t 0)
    (Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hU : ∀ t, 0 < t → t < d.threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hinc : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - initial t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤
        ENNReal.ofReal (actualProbeCenterC1Constant d.threshold Cref Cinc Ctail *
          t ^ (10 : ℕ)) := by
  apply actual_probe_center_C1_ten_bound A hA F₀ hF₀ U₀ d.map d.threshold
    Cref Cinc Ctail hCref hCinc hCtail href hU
  · intro t ht htt
    exact actualFamily_slice_smooth_of_joint (d.map t) d.radius
      (d.joint_smooth t ht htt) 0 (by simpa using d.radius_pos)
  · exact hinc
  · intro t ht htt
    rw [← hidentity t ht htt]
    exact htail t ht htt

/-- The true G0+U0 initial identity and literal actual repair tail yield
order-ten control of exactly the previously constructed polar Q. The genuine
parameter C1 budget supplies the remaining whole-ball displacement term. -/
def NativeProbeDomainData.chosenNormalGapOfActualInitial [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (initial U₀ : ℝ → ProbeParameters r → M → V)
    (hidentity : ∀ t, 0 < t → t < d.threshold →
      initial t 0 = actualProbeFirstMap F₀ U₀ t 0)
    (Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hU : ∀ t, 0 < t → t < d.threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hinc : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - initial t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.chosenNormalGapOfCenterTen (actualProbeCenterC1Constant d.threshold Cref Cinc Ctail)
    (actualProbeCenterC1Constant_nonneg d.threshold hCref hCinc hCtail)
    (d.actual_center_originalC1_of_initial initial U₀ hidentity
      Cref Cinc Ctail hCref hCinc hCtail href hU hinc htail)

/-- The modulus has all four real contributions: reference contraction,
full initial increment, actual repair tail and parameter displacement.
No final-center estimate is among the premises. -/
@[simp] theorem NativeProbeDomainData.chosenNormalGapOfActualInitial_gap [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (initial U₀ : ℝ → ProbeParameters r → M → V)
    (hidentity : ∀ t, 0 < t → t < d.threshold →
      initial t 0 = actualProbeFirstMap F₀ U₀ t 0)
    (Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hU : ∀ t, 0 < t → t < d.threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hinc : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - initial t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    (d.chosenNormalGapOfActualInitial initial U₀ hidentity
      Cref Cinc Ctail hCref hCinc hCtail href hU hinc htail).gap =
      fun t ↦ 4 * nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ *
        ((actualProbeCenterC1Constant d.threshold Cref Cinc Ctail +
          probeParameterDisplacementConstant n N * d.constant * d.radius) *
            |t| ^ (10 : ℕ)) := rfl

/-- The model-plus-literal-correction route consumes the same actual
initial map identity. Its model is never silently identified with G1. -/
def NativeProbeDomainModelData.chosenNormalGapOfActualInitial [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (initial U₀ : ℝ → ProbeParameters r → M → V)
    (hidentity : ∀ t, 0 < t → t < d.threshold →
      initial t 0 = actualProbeFirstMap F₀ U₀ t 0)
    (Cref Cinc Ctail : ℝ) (hCref : 0 ≤ Cref) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (href : probeAtlasCj A 1 F₀ ≤ ENNReal.ofReal Cref)
    (hU : ∀ t, 0 < t → t < d.threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hinc : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - initial t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.toDomainData.chosenNormalGapOfActualInitial initial U₀ hidentity
    Cref Cinc Ctail hCref hCinc hCtail href hU hinc htail

end GlobalEmbedding.NormalPolar
