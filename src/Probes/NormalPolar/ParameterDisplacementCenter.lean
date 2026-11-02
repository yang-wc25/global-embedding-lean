import NormalPolar.ParameterDisplacement
import NormalPolar.ProbeC1Gap

/-!
# Actual center defects and the original t^10 same-Q gap

The parameter derivative estimate does not force the center slice to be the
reference immersion. This file keeps its actual spatial C1 defect as a
separate term, then proves the whole-ball displacement and same-Q gap from
that term and the genuine original parameter C1 field. No zero-center
assumption, change of Q, smaller ball or smaller threshold occurs.
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

/-- A fixed original threshold absorbs the extra two powers. Unlike the
usual small-scale shortcut, this requires no t ≤ 1 and keeps the entire
original scale interval. -/
theorem pow_twelve_le_threshold_sq_mul_pow_ten
    (threshold t : ℝ) (ht : 0 < t) (htt : t < threshold) :
    t ^ (12 : ℕ) ≤ (max 1 threshold) ^ (2 : ℕ) * t ^ (10 : ℕ) := by
  have htmax : t ≤ max 1 threshold := htt.le.trans (le_max_right _ _)
  calc
    t ^ (12 : ℕ) = t ^ (2 : ℕ) * t ^ (10 : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htmax 2)
      (pow_nonneg ht.le _)

/-- A true original C1 center bound of order twelve yields order ten on
the entire given scale interval, with an explicitly threshold-dependent
constant chosen before the scale. -/
theorem originalC1_center_ten_of_twelve
    (A : BufferedAtlas M E) {r : ℕ} (F₀ : M → V)
    (F : ℝ → ProbeParameters r → M → V)
    (threshold C : ℝ) (hC : 0 ≤ C)
    (hcenter : ∀ t, 0 < t → t < threshold →
      probeAtlasCj A 1 (F t 0 - F₀) ≤ ENNReal.ofReal (C * t ^ (12 : ℕ))) :
    ∀ t, 0 < t → t < threshold →
      probeAtlasCj A 1 (F t 0 - F₀) ≤
        ENNReal.ofReal ((C * (max 1 threshold) ^ (2 : ℕ)) * t ^ (10 : ℕ)) := by
  intro t ht htt
  apply (hcenter t ht htt).trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (pow_twelve_le_threshold_sq_mul_pow_ten threshold t ht htt) hC

/-- The existing finite actual-map telescoping theorem gives the original
norm triangle with exact original support sets and no conversion loss. -/
theorem probeAtlasCj_three_point_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (j : ℕ)
    (F₀ F₁ F₂ : M → V)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF₁ : ContMDiff IM 𝓘(ℝ, V) ∞ F₁)
    (hF₂ : ContMDiff IM 𝓘(ℝ, V) ∞ F₂)
    {b₀ b₁ : ℝ} (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (h₀ : probeAtlasCj A j (F₁ - F₀) ≤ ENNReal.ofReal b₀)
    (h₁ : probeAtlasCj A j (F₂ - F₁) ≤ ENNReal.ofReal b₁) :
    probeAtlasCj A j (F₂ - F₀) ≤ ENNReal.ofReal (b₀ + b₁) := by
  let F : ℕ → M → V := fun k ↦ if k = 0 then F₀ else if k = 1 then F₁ else F₂
  let b : ℕ → ℝ := fun k ↦ if k = 0 then b₀ else b₁
  have hs (k : ℕ) (hk : k ≤ 2) : ContMDiff IM 𝓘(ℝ, V) ∞ (F k) := by
    interval_cases k <;> simp only [F] <;> assumption
  have hb (k : ℕ) (hk : k < 2) : 0 ≤ b k := by
    interval_cases k <;> simp only [b] <;> assumption
  have hstep (k : ℕ) (hk : k < 2) :
      probeAtlasCj A j (F (k + 1) - F k) ≤ ENNReal.ofReal (b k) := by
    interval_cases k
    · simpa [F, b] using h₀
    · simpa [F, b] using h₁
  have h := finite_probeAtlas_prefix_budget A hA j 2 F hs b hb hstep 2 le_rfl
  simpa [F, b, Finset.sum_range_succ] using h

namespace NativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- The actual center defect is retained additively. The displacement term
is derived from parameter_C1 on the original ball, not supplied as a premise. -/
theorem originalC1_displacement_from_center
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    {b : ℝ} (hb : 0 ≤ b)
    (hcenter : probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal b)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) :
    probeAtlasCj A 1 (d.map t u - F₀) ≤
      ENNReal.ofReal (b + probeParameterDisplacementConstant n N * d.constant *
        t ^ (10 : ℕ) * ‖u‖) := by
  have hzero : ‖(0 : ProbeParameters r)‖ < d.radius := by simpa using d.radius_pos
  have hp := originalC1_parameter_displacement d.geometry A hA hcover t ht htt
    (mul_nonneg d.constant_nonneg (pow_nonneg ht.le (10 : ℕ)))
    (fun v hv a ↦ d.parameter_C1 t ht htt v hv a) u 0 hu hzero
  simp only [geometry_map, sub_zero, mul_assoc] at hp
  apply probeAtlasCj_three_point_bound A hA 1 F₀ (d.map t 0) (d.map t u)
    hF₀ (d.slice_smooth t 0) (d.slice_smooth t u) hb
    (mul_nonneg (mul_nonneg (mul_nonneg (probeParameterDisplacementConstant_nonneg n N)
      d.constant_nonneg) (pow_nonneg ht.le _)) (norm_nonneg u)) hcenter
  simpa only [mul_assoc] using hp

/-- The full spatial displacement coefficient consists of the genuine
center coefficient plus the derived parameter variation over the original
radius. All terms precede t, u and source points. -/
def spatialC1ConstantFromCenter
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (Ccenter : ℝ) : ℝ :=
  Ccenter + probeParameterDisplacementConstant n N * d.constant * d.radius

theorem spatialC1ConstantFromCenter_nonneg
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    {Ccenter : ℝ} (hCcenter : 0 ≤ Ccenter) : 0 ≤ d.spatialC1ConstantFromCenter Ccenter :=
  add_nonneg hCcenter
    (mul_nonneg (mul_nonneg (probeParameterDisplacementConstant_nonneg n N) d.constant_nonneg)
      d.radius_pos.le)

/-- A real center t^10 budget and the original parameter_C1 estimate imply
the full t^10 spatial C1 budget on the entire original ball and threshold. -/
theorem originalC1_displacement_of_center_ten
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      probeAtlasCj A 1 (d.map t u - F₀) ≤
        ENNReal.ofReal (d.spatialC1ConstantFromCenter Ccenter * t ^ (10 : ℕ)) := by
  intro t ht htt u hu
  have h := d.originalC1_displacement_from_center t ht htt
    (mul_nonneg hCcenter (pow_nonneg ht.le _)) (hcenter t ht htt) u hu
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hk : 0 ≤ probeParameterDisplacementConstant n N * d.constant * t ^ (10 : ℕ) :=
    mul_nonneg (mul_nonneg (probeParameterDisplacementConstant_nonneg n N) d.constant_nonneg)
      (pow_nonneg ht.le _)
  calc
    _ ≤ Ccenter * t ^ (10 : ℕ) +
        probeParameterDisplacementConstant n N * d.constant * t ^ (10 : ℕ) * d.radius :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hu.le hk)
    _ = d.spatialC1ConstantFromCenter Ccenter * t ^ (10 : ℕ) := by
      unfold spatialC1ConstantFromCenter
      ring

/-- The sharper certificate belongs to the same full probe and Q. The only
new input is the actual center's spatial C1 defect, which is not discarded. -/
def chosenNormalGapOfCenterTen [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    ChosenProbeNormalGap d.toExactProbeFamily :=
  d.chosenNormalGapOfC1Ten (d.spatialC1ConstantFromCenter Ccenter)
    (d.spatialC1ConstantFromCenter_nonneg hCcenter)
    (d.originalC1_displacement_of_center_ten Ccenter hCcenter hcenter)

@[simp] theorem chosenNormalGapOfCenterTen_gap [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (10 : ℕ))) :
    (d.chosenNormalGapOfCenterTen Ccenter hCcenter hcenter).gap =
      fun t ↦ 4 * nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ *
        (d.spatialC1ConstantFromCenter Ccenter * |t| ^ (10 : ℕ)) := rfl

/-- The actual repair center may carry the stronger order-twelve tail.
This consumes that real budget without changing the original threshold. -/
def chosenNormalGapOfCenterTwelve [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (Ccenter : ℝ) (hCcenter : 0 ≤ Ccenter)
    (hcenter : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - F₀) ≤ ENNReal.ofReal (Ccenter * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap d.toExactProbeFamily :=
  d.chosenNormalGapOfCenterTen (Ccenter * (max 1 d.threshold) ^ (2 : ℕ))
    (mul_nonneg hCcenter (sq_nonneg _))
    (originalC1_center_ten_of_twelve A F₀ d.map d.threshold Ccenter hCcenter hcenter)

end NativeProbeData
end GlobalEmbedding.NormalPolar
