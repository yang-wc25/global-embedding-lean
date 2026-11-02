import NormalPolar.GapOperator
import NormalPolar.GapProjection
import Round2.ProbeNormalGap

/-!
# The same explicit polar Q supplies the original normal-gap field

Every estimate below concerns `probe.normalIdentification` itself. The formula
hypothesis identifies that field with the explicit analytic polar construction;
it is an equality of the actual operators, not a bound on the desired gap.
The construction files supply this equality for their actual normal isometry.

The original threshold and parameter radius are retained. At scales where the
small-projection estimate is unavailable, the norm-one bound of the very same
normal isometry gives the bound two. This only uses the already existing
normal identification at such scales and never manufactures an unidentified Q.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

/-- A global nonnegative modulus with the useful small-scale branch. -/
def polarGapModulus (C : ℝ) (ε : ℝ → ℝ) (t : ℝ) : ℝ :=
  if ε t ≤ (1 / 2 : ℝ) then C * (ε t) ^ 2 + ε t else 2

theorem polarGapModulus_nonneg (C : ℝ) (hC : 0 ≤ C) (ε : ℝ → ℝ)
    (hε : ∀ t, 0 ≤ ε t) (t : ℝ) : 0 ≤ polarGapModulus C ε t := by
  unfold polarGapModulus
  split_ifs
  · exact add_nonneg (mul_nonneg hC (sq_nonneg _)) (hε t)
  · norm_num

theorem polarGapModulus_tendsto (C : ℝ) (ε : ℝ → ℝ)
    (hε : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (polarGapModulus C ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ε t ≤ (1 / 2 : ℝ) :=
    ((tendsto_order.mp hε).2 (1 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hpoly : Tendsto (fun t ↦ C * (ε t) ^ 2 + ε t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((hε.pow 2).const_mul C).add hε
  apply hpoly.congr'
  filter_upwards [hsmall] with t ht
  simp only [polarGapModulus, ite_eq_left ht]

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A true-projection budget and the equality to the explicitly constructed
operator produce the actual original `ChosenProbeNormalGap` record. Every
quantifier is on the original probe's scale interval, parameter ball and atlas.
No gap of Q is an input. -/
def chosenProbeNormalGapOfProjectionBudget
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (ε : ℝ → ℝ) (hε : ∀ t, 0 ≤ ε t)
    (hεlim : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hprojection : ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
      ∀ i z, z ∈ A.support i →
        ‖(normalSpace (I := IM) (probe.map t u) z).starProjection -
          (normalSpace (I := IM) F₀ z).starProjection‖ ≤ ε t)
    (hformula : ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
      ∀ i z, z ∈ A.support i →
        ‖(normalSpace (I := IM) (probe.map t u) z).starProjection -
          (normalSpace (I := IM) F₀ z).starProjection‖ < 1 →
        normalIdentificationOperator (n := n) F₀ (probe.map t u)
          (probe.normalIdentification t u) z =
        actualPolarOperator (normalSpace (I := IM) F₀ z).starProjection
          (normalSpace (I := IM) (probe.map t u) z).starProjection) :
    ChosenProbeNormalGap probe := by
  let h := exists_actualPolarOperator_gap_bound («V» := V)
  let C := h.choose
  have hC : 0 ≤ C := h.choose_spec.1
  have hbound := h.choose_spec.2
  refine {
    gap := polarGapModulus C ε
    gap_nonneg := polarGapModulus_nonneg C hC ε hε
    gap_tendsto := polarGapModulus_tendsto C ε hεlim
    gap_bound := ?_ }
  intro t ht htt u hu i z hz
  by_cases hsmall : ε t ≤ (1 / 2 : ℝ)
  · have hgap := hprojection t ht htt u hu i z hz
    have hclose : ‖(normalSpace (I := IM) (probe.map t u) z).starProjection -
        (normalSpace (I := IM) F₀ z).starProjection‖ < 1 :=
      (hgap.trans hsmall).trans_lt (by norm_num)
    rw [hformula t ht htt u hu i z hz hclose, polarGapModulus, ite_eq_left hsmall]
    exact hbound _ _ (normalSpace (I := IM) F₀ z).isIdempotentElem_starProjection
      (normalSpace (I := IM) F₀ z).starProjection_norm_le
      (normalSpace (I := IM) (probe.map t u) z).starProjection_norm_le
      (ε t) (hε t) hsmall hgap
  · rw [polarGapModulus, ite_eq_right hsmall]
    calc
      _ ≤ ‖normalIdentificationOperator (n := n) F₀ (probe.map t u)
          (probe.normalIdentification t u) z‖ +
          ‖(normalSpace (I := IM) F₀ z).starProjection‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
        (normalIdentificationOperator_norm_le_one F₀ (probe.map t u)
          (probe.normalIdentification t u) z)
        (normalSpace (I := IM) F₀ z).starProjection_norm_le
      _ = 2 := by norm_num

/-- The full same-Q gap follows from the probe's already required actual
metric and original C² bounds. No additional projection-closeness budget is
supplied: compact reference geometry and the real first jets construct it.
The equality hypothesis is supplied by selecting this very polar Q upstream;
no existing second-form response is transported to a different Q. -/
def chosenProbeNormalGapOfOriginalC2
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (hformula : ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
      ∀ i z, z ∈ A.support i →
        ‖(normalSpace (I := IM) (probe.map t u) z).starProjection -
          (normalSpace (I := IM) F₀ z).starProjection‖ < 1 →
        normalIdentificationOperator (n := n) F₀ (probe.map t u)
          (probe.normalIdentification t u) z =
        actualPolarOperator (normalSpace (I := IM) F₀ z).starProjection
          (normalSpace (I := IM) (probe.map t u) z).starProjection) :
    ChosenProbeNormalGap probe := by
  let h := exists_uniform_sameMetric_normalProjection_budget A hA hcompact F₀ hF₀ himm
  let K := h.choose
  have hK : 0 < K := h.choose_spec.1
  have hbudget := h.choose_spec.2
  let ε : ℝ → ℝ := fun t ↦ K * (probe.constant * |t| ^ ((44 : ℝ) / 5))
  have hε : ∀ t, 0 ≤ ε t := by
    intro t
    exact mul_nonneg hK.le (mul_nonneg probe.constant_nonneg (Real.rpow_nonneg (abs_nonneg t) _))
  have hsigma : Tendsto (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (q := (44 : ℝ) / 5)
      (by positivity)).comp continuous_abs).tendsto (0 : ℝ)
    simpa only [Function.comp_def, abs_zero, Real.zero_rpow (by norm_num : (44 : ℝ) / 5 ≠ 0)] using
      h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hεlim : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [ε] using (hsigma.const_mul probe.constant).const_mul K
  refine chosenProbeNormalGapOfProjectionBudget probe ε hε hεlim ?_ hformula
  intro t ht htt u hu i z hz
  have h := hbudget (probe.map t u) (probe.slice_smooth t u) (probe.metric t ht htt u hu)
    (probe.constant * t ^ ((44 : ℝ) / 5))
    (mul_nonneg probe.constant_nonneg (Real.rpow_nonneg ht.le _))
    (probe.closeness t ht htt u hu) i z hz
  simpa only [ε, abs_of_pos ht] using h

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.polarGapModulus_nonneg
#print axioms GlobalEmbedding.NormalPolar.polarGapModulus_tendsto
#print axioms GlobalEmbedding.NormalPolar.chosenProbeNormalGapOfProjectionBudget
#print axioms GlobalEmbedding.NormalPolar.chosenProbeNormalGapOfOriginalC2
