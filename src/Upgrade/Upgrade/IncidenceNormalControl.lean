import Upgrade.IncidenceActualFormCloseness
import Upgrade.CompactScaleSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Exact remaining quantitative boundary for the selected normal identification

The original full probe record contains smooth orthogonal identifications and
the four response estimates. The proof after (8.4) chooses a particular polar
identification. This record isolates the two further consequences of that
choice needed by the geometric consumers: a vanishing ambient identification
gap and a uniform spatial first derivative in the original atlas.

There is deliberately NO constructor for this record here. It belongs to the
upstream selected-normal-identification work. No field asserts an incidence
rank, bad-set removal, injectivity or the upgrade conclusion. The theorem below
derives actual identified-form closeness from these precise inputs and the
original full probes C² estimate, including the real source normalization.
-/

noncomputable section
open Function Filter Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Quantitative consequences of the actual polar identification selected
upstream. The spatial derivative is the native derivative of that very same
ambient operator in the same actual atlas chart. -/
structure ChosenProbeNormalControl
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) where
  gap : ℝ → ℝ
  gap_nonneg : ∀ t, 0 ≤ gap t
  gap_tendsto : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0)
  spatialBound : ℝ
  spatialBound_nonneg : 0 ≤ spatialBound
  gap_bound : ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
    ∀ i z, z ∈ A.support i →
      ‖normalIdentificationOperator (n := n) F₀ (probe.map t u)
          (probe.normalIdentification t u) z -
        (normalSpace (I := IM) F₀ z).starProjection‖ ≤ gap t
  spatial_derivative_bound : ∀ t, 0 < t → t < probe.threshold →
    ∀ u, ‖u‖ < probe.radius → ∀ i z, z ∈ A.support i →
      ‖fderiv ℝ
        (fun s : E ↦ normalIdentificationOperator (n := n) F₀ (probe.map t u)
          (probe.normalIdentification t u) ((A.chart i).symm s)) (A.chart i z)‖ ≤ spatialBound

/-- The actual old fixed-atlas Hessians have one finite bound on every compact
support, including empty supports. No global tangent trivialization is used. -/
theorem exists_reference_hessian_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) :
    ∃ H > 0, ∀ i z, z ∈ A.support i → ‖probeAtlasSecondJet A F₀ i z‖ ≤ H := by
  choose H hH using fun i ↦ (hcompact i).exists_bound_of_continuousOn
    ((continuousOn_probeAtlasSecondJet A hA F₀ hF₀ i).mono (hA.support_subset i))
  obtain ⟨C, hC⟩ := Finite.exists_le H
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro i z hz
  exact (hH i z hz).trans ((hC i).trans ((le_abs_self C).trans (by linarith)))

/-- For every actual packet center, one small scale works uniformly over the
entire admitted parameter ball and its original atlas support. This is the
actual C⁰ input to the fixed Schur-block and supported-chart margins. -/
theorem ChosenProbeNormalControl.eventually_actual_form_close
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalControl probe)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ → ∀ u, ‖u‖ < probe.radius →
      ∀ z, z ∈ A.support i →
      ‖actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hx (u, A.chart i z) -
        normalizedReferenceForm A hA F₀ i x hx z‖ < delta := by
  obtain ⟨H, hH, hHbound⟩ := exists_reference_hessian_bound A hA hcompact F₀ hF₀
  let L := actualHessianLiftConstant E V * probeAtlasDerivativeConstant n N 2
  let K := ‖probeAtlasNormalizationSquare A hA i x hx‖
  have hsigma : Tendsto (fun t : ℝ ↦ t ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuous_rpow_const (q := (44 : ℝ) / 5)
      (by positivity)).tendsto (0 : ℝ)
    simpa only [Real.zero_rpow (by norm_num : (44 : ℝ) / 5 ≠ 0)] using
      h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hbound : Tendsto
      (fun t ↦ (L * (probe.constant * t ^ ((44 : ℝ) / 5)) + control.gap t * H) * K)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (((hsigma.const_mul probe.constant).const_mul L).add
        (control.gap_tendsto.mul_const H)).mul_const K
  have hev := (tendsto_order.mp hbound).2 delta hdelta
  obtain ⟨s, hs, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  refine ⟨min s probe.threshold, lt_min hs probe.threshold_pos, min_le_right _ _, ?_⟩
  intro t ht ht₀ u hu z hz
  have hts : t < s := ht₀.trans_le (min_le_left _ _)
  have htt : t < probe.threshold := ht₀.trans_le (min_le_right _ _)
  have hc := probe.actual_form_sub_reference_bound hA t ht htt u hu i x hx z hz
  have hg := control.gap_bound t ht htt u hu i z hz
  have hprod := mul_le_mul hg (hHbound i z hz) (norm_nonneg _) (control.gap_nonneg t)
  exact (hc.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hprod)
    (norm_nonneg _))).trans_lt (hsmall ⟨ht, hts⟩)

#print axioms exists_reference_hessian_bound
#print axioms ChosenProbeNormalControl.eventually_actual_form_close

end GlobalEmbedding.Upgrade
