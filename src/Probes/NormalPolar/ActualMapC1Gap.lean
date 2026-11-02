import NormalPolar.OriginalC1Gap
import NormalPolar.ActualMapGlobalLinearGap

/-!
# Same actual Q: the zero-order gap from genuine spatial C¹ displacement

Only the first jet of F-F₀ is needed. The unchanged total normal identification
has gap at most 4*K1*b(t) on the original sets, where K1 depends only on the
fixed reference immersion and atlas. No Q, Q-gap, or Q-smoothness assumption is input.
A stronger rate requires a genuinely stronger displacement budget, not merely
the original parameter C¹ response bound or an unproved center identity.
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

/-- A true original C¹ budget directly gives the explicit whole-source
same-total-Q bound, regardless of whether the reference coefficient times b is below one. -/
theorem actualImmersionNormalIdentification_gap_originalC1_linear
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b) (hbudget : probeAtlasCj A 1 (F - F₀) ≤ ENNReal.ofReal b)
    (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ F
        (actualImmersionNormalIdentification F₀ F hi₀ hi) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        (4 * nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀) * b := by
  apply (norm_actualImmersionNormalIdentification_sub_projection_le_four F₀ F hi₀ hi x).trans
  have hp := sameMetric_normalProjection_gap_originalC1 A hA hcompact hcover F₀ hF₀ hi₀
    F hF hmetric b hb hbudget x
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4)

/-- Direct actual-family output before any `ExactProbeFamily` exists.
The original arbitrary scale/parameter sets are retained, and the explicit
linear modulus controls the same total Q at every source point. There is no
uniform q<1 hypothesis or tacit restriction to small scales. -/
theorem total_sameQ_globalLinear_gap_of_actual_maps_originalC1
    {P : Type*} (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : ℝ → P → M → V)
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (T : Set ℝ) (U : Set P)
    (hF : ∀ t ∈ T, ∀ u ∈ U, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hmetric : ∀ t ∈ T, ∀ u ∈ U, ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hblim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ t ∈ T, ∀ u ∈ U,
      probeAtlasCj A 1 (F t u - F₀) ≤ ENNReal.ofReal (b t)) :
    let g := totalNormalLinearGap (nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀) b
    (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t ∈ T, ∀ u ∈ U, ∀ x,
        ‖normalIdentificationOperator (n := n) F₀ (F t u)
            (actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)) x -
          (normalSpace (I := IM) F₀ x).starProjection‖ ≤ g t := by
  refine ⟨totalNormalLinearGap_nonneg _
    (nativeReferenceResponseFactor_pos A hA hcompact F₀ hF₀ hi₀).le b hb,
    totalNormalLinearGap_tendsto _ b hblim, ?_⟩
  intro t ht u hu x
  exact actualImmersionNormalIdentification_gap_originalC1_linear A hA hcompact hcover
    F₀ hF₀ hi₀ (F t u) (hF t ht u hu) (hi t u) (hmetric t ht u hu)
    (b t) (hb t) (hbudget t ht u hu) x

end GlobalEmbedding.NormalPolar
