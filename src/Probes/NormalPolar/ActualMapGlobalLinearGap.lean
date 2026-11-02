import NormalPolar.GlobalLinearGap
import NormalPolar.OriginalMapGeometry

/-!
# An explicit same-total-Q gap from actual original C² budgets

The modulus is exactly 4*K0*b(t), with K0 fixed by the reference immersion
and original covering atlas. No uniform reserve, smallness assumption,
joint-smoothness assumption on Q, or reduction of the supplied domains is
needed for this zeroth-order conclusion. The normal identification is the
same total actual canonical field at every parameter, including its far branch.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

/-- The completely specified linear modulus, with no piecewise cutoff or
compactness-selected polar-response coefficient. -/
def totalNormalLinearGap (K : ℝ) (b : ℝ → ℝ) (t : ℝ) : ℝ := 4 * K * b t

theorem totalNormalLinearGap_nonneg (K : ℝ) (hK : 0 ≤ K) (b : ℝ → ℝ)
    (hb : ∀ t, 0 ≤ b t) (t : ℝ) : 0 ≤ totalNormalLinearGap K b t :=
  mul_nonneg (mul_nonneg (by norm_num) hK) (hb t)

theorem totalNormalLinearGap_tendsto (K : ℝ) (b : ℝ → ℝ)
    (hlim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (totalNormalLinearGap K b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  change Tendsto (fun t ↦ 4 * K * b t) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero] using hlim.const_mul (4 * K)

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The same actual total identification of two actual immersions satisfies
the global reference-gap estimate without a projection-gap assumption. -/
theorem norm_actualImmersionNormalIdentification_sub_projection_le_four
    (F₀ F : M → V)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ F
        (actualImmersionNormalIdentification F₀ F hi₀ hi) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        4 * ‖(normalSpace (I := IM) F₀ x).starProjection -
          (normalSpace (I := IM) F x).starProjection‖ :=
  norm_totalNormalPolarEquiv_operator_sub_projection_le_four
    (normalSpace (I := IM) F₀ x) (normalSpace (I := IM) F x)
    (actualMap_normalRanks_eq F₀ F hi₀ hi x)

/-- A true original C² budget directly gives the explicit whole-source
same-total-Q bound, regardless of whether K0*b is below one. -/
theorem actualImmersionNormalIdentification_gap_originalC2_linear
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b) (hbudget : probeAtlasCj A 2 (F - F₀) ≤ ENNReal.ofReal b)
    (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ F
        (actualImmersionNormalIdentification F₀ F hi₀ hi) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤
        (4 * originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀) * b := by
  apply (norm_actualImmersionNormalIdentification_sub_projection_le_four F₀ F hi₀ hi x).trans
  have hp := originalC2PolarConstant_projection_bound A hA hcompact hcover F₀ hF₀ hi₀
    F hF hmetric b hb hbudget x
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4)

/-- Direct actual-family output before any `ExactProbeFamily` exists.
The original arbitrary scale/parameter sets are retained, and the explicit
linear modulus controls the same total Q at every source point. There is no
uniform q<1 hypothesis or tacit restriction to small scales. -/
theorem total_sameQ_globalLinear_gap_of_actual_maps_originalC2
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
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (b t)) :
    let g := totalNormalLinearGap (originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀) b
    (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t ∈ T, ∀ u ∈ U, ∀ x,
        ‖normalIdentificationOperator (n := n) F₀ (F t u)
            (actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)) x -
          (normalSpace (I := IM) F₀ x).starProjection‖ ≤ g t := by
  refine ⟨totalNormalLinearGap_nonneg _
    (originalC2PolarConstant_pos A hA hcompact hcover F₀ hF₀ hi₀).le b hb,
    totalNormalLinearGap_tendsto _ b hblim, ?_⟩
  intro t ht u hu x
  exact actualImmersionNormalIdentification_gap_originalC2_linear A hA hcompact hcover
    F₀ hF₀ hi₀ (F t u) (hF t ht u hu) (hi t u) (hmetric t ht u hu)
    (b t) (hb t) (hbudget t ht u hu) x

end GlobalEmbedding.NormalPolar
