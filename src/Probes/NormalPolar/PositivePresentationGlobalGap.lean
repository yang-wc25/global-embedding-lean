import NormalPolar.IdentificationTransportPositive
import NormalPolar.ActualMapGlobalLinearGap

/-!
# A global linear gap for the original positively presented probe

The existing probe and its actual Q are retained. Near the reference normal
space, positive-root uniqueness identifies this actual Q with the explicit
polar formula. Away from that neighborhood, this very original Q has ambient
norm at most one. Consequently its gap is globally bounded by four times the
true projection difference, with no common reserve. The explicit C² modulus
is attached directly as `ChosenProbeNormalGap p`; no probe reconstruction,
normal-field replacement or second-form-response transport is performed.
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

/-- The actual original Q supplied with a genuine positive compression
presentation has a global linear reference gap. Only the near branch uses
positive-root uniqueness; the far branch uses the original Q's isometry. -/
theorem PositiveProbeNormalPresentation.operator_gap_le_four
    {F₀ : M → V} {r : ℕ} {p : ProbeGeometry (n := n) F₀ r}
    (presentation : PositiveProbeNormalPresentation p)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius) (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        4 * ‖(normalSpace (I := IM) F₀ x).starProjection -
          (normalSpace (I := IM) (p.map t u) x).starProjection‖ := by
  by_cases hsmall : ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) (p.map t u) x).starProjection‖ ≤ (1 / 2 : ℝ)
  · have hclose : ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (p.map t u) x).starProjection‖ < 1 :=
      hsmall.trans_lt (by norm_num)
    rw [presentation.operator_eq_polar t ht htt u hu x hclose]
    have h := norm_actualPolarOperator_sub_projection_le_explicit
      (normalSpace (I := IM) F₀ x) (normalSpace (I := IM) (p.map t u) x)
      (1 / 2 : ℝ) (by norm_num) hsmall
    norm_num at h
    have hnonneg := norm_nonneg ((normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) (p.map t u) x).starProjection)
    have hmul := mul_le_mul_of_nonneg_left hsmall hnonneg
    nlinarith
  · have hlarge : (1 / 2 : ℝ) < ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (p.map t u) x).starProjection‖ := lt_of_not_ge hsmall
    have hbound := (norm_sub_le
      (normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x)
      (normalSpace (I := IM) F₀ x).starProjection).trans
        (add_le_add (normalIdentificationOperator_norm_le_one F₀ (p.map t u)
          (p.normalIdentification t u) x) (normalSpace (I := IM) F₀ x).starProjection_norm_le)
    linarith

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- Any genuine original C² budget gives a whole-source bound for the
original positively presented Q. It need not be a small budget. -/
theorem positivePresentation_gap_originalC2_linear
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius)
    (b : ℝ) (hb : 0 ≤ b) (hbudget : probeAtlasCj A 2 (p.map t u - F₀) ≤ ENNReal.ofReal b)
    (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        (4 * originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀) * b := by
  apply (presentation.operator_gap_le_four t ht htt u hu x).trans
  have hp := originalC2PolarConstant_projection_bound A hA hcompact hcover F₀ hF₀ hi₀
    (p.map t u) (p.slice_smooth t u) (p.metric t ht htt u hu) b hb hbudget x
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4)

/-- The explicit original-scale modulus for the original complete record.
It depends on reference geometry and p's original C² constant, not a reserve. -/
def positivePresentationGlobalGap
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves) (t : ℝ) : ℝ :=
  (4 * originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * p.constant) *
    |t| ^ ((44 : ℝ) / 5)

theorem positivePresentationGlobalGap_nonneg
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves) (t : ℝ) :
    0 ≤ positivePresentationGlobalGap hA hcompact hcover hi₀ p t := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (originalC2PolarConstant_pos A hA hcompact hcover F₀ hF₀ hi₀).le) p.constant_nonneg)
      (Real.rpow_nonneg (abs_nonneg t) _)

theorem positivePresentationGlobalGap_tendsto
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves) :
    Tendsto (positivePresentationGlobalGap hA hcompact hcover hi₀ p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5)) :=
    (Real.continuous_rpow_const (by norm_num : 0 ≤ (44 : ℝ) / 5)).comp continuous_abs
  have hp : Tendsto (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  change Tendsto (fun t ↦ (4 * originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ *
    p.constant) * |t| ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero] using hp.const_mul
    (4 * originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * p.constant)

/-- The explicit modulus bounds this original Q on the whole unchanged
admitted parameter domain and all source points. The record and its existing
second-form response are never reconstructed. -/
theorem positivePresentationGlobalGap_bound
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius) (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        positivePresentationGlobalGap hA hcompact hcover hi₀ p t := by
  have h := positivePresentation_gap_originalC2_linear hA hcompact hcover hi₀ p presentation
    t ht htt u hu (p.constant * t ^ ((44 : ℝ) / 5))
    (mul_nonneg p.constant_nonneg (Real.rpow_nonneg ht.le _))
    (p.closeness t ht htt u hu) x
  simpa only [positivePresentationGlobalGap, abs_of_pos ht, mul_assoc] using h

/-- Direct same-Q certificate for the original full probe. The return type
is `ChosenProbeNormalGap p`, not a probe rebuilt with a canonical field. -/
def chosenProbeNormalGapOfPositivePresentationGlobalLinear
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    ChosenProbeNormalGap p where
  gap := positivePresentationGlobalGap hA hcompact hcover hi₀ p
  gap_nonneg := positivePresentationGlobalGap_nonneg hA hcompact hcover hi₀ p
  gap_tendsto := positivePresentationGlobalGap_tendsto hA hcompact hcover hi₀ p
  gap_bound := fun t ht htt u hu _i x _hx ↦
    positivePresentationGlobalGap_bound hA hcompact hcover hi₀ p presentation t ht htt u hu x

@[simp] theorem chosenProbeNormalGapOfPositivePresentationGlobalLinear_gap
    (hA : IsSmoothBufferedAtlas A) (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    (chosenProbeNormalGapOfPositivePresentationGlobalLinear hA hcompact hcover hi₀ p presentation).gap =
      positivePresentationGlobalGap hA hcompact hcover hi₀ p := rfl

end GlobalEmbedding.NormalPolar
