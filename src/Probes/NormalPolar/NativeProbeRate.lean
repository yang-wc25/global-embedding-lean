import NormalPolar.GapLipschitz
import NormalPolar.NativeProbeConstruction

/-!
# An explicit original-scale modulus for the same constructed probe

The true C² closeness, exact metric and fixed reserve give a whole-source
O(t^(44/5)) gap for exactly the normal identification already used by the
full original probe. The source map and original parameter domain do not
change, and no estimate on Q is an input.
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

namespace NativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- One scalar constant, fixed before the scale, parameter and source point. -/
def gapRateConstant (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) : ℝ :=
  polarResponseConstantOn V d.reserve d.reserve_lt_one *
    originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * d.constant

theorem gapRateConstant_nonneg
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    0 ≤ d.gapRateConstant := by
  exact mul_nonneg
    (mul_nonneg (polarResponseConstantOn_nonneg d.reserve d.reserve_lt_one)
      (originalC2PolarConstant_pos A hA hcompact hcover F₀ hF₀ hi₀).le)
    d.constant_nonneg

/-- A total nonnegative modulus with the original positive-scale power. -/
def normalGapWithRate
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ) : ℝ :=
  d.gapRateConstant * |t| ^ ((44 : ℝ) / 5)

theorem normalGapWithRate_nonneg
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ) :
    0 ≤ d.normalGapWithRate t :=
  mul_nonneg d.gapRateConstant_nonneg (Real.rpow_nonneg (abs_nonneg t) _)

theorem normalGapWithRate_tendsto
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    Tendsto d.normalGapWithRate (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := d.closenessBudget_tendsto.const_mul
    (polarResponseConstantOn V d.reserve d.reserve_lt_one *
      originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀)
  change Tendsto (fun t : ℝ ↦ d.gapRateConstant * |t| ^ ((44 : ℝ) / 5))
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [normalGapWithRate, gapRateConstant, closenessBudget, mul_assoc, mul_zero] using h

/-- The linear-rate estimate holds at every source point, uniformly on the
unchanged parameter ball and scale interval. -/
theorem normalGapWithRate_bound
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ (d.geometry.map t u)
      (d.geometry.normalIdentification t u) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤ d.normalGapWithRate t := by
  change ‖normalIdentificationOperator (n := n) F₀ (d.map t u)
    (actualImmersionNormalIdentification F₀ (d.map t u) hi₀ (d.immersion t u)) x -
    (normalSpace (I := IM) F₀ x).starProjection‖ ≤ _
  rw [actualImmersionNormalIdentification_operator F₀ (d.map t u) hi₀ (d.immersion t u) x
    ((d.projection_gap t ht htt u hu x).trans_lt d.reserve_lt_one)]
  have hlinear := norm_actualNormalPolarOperator_sub_projection_le_reserve
    d.reserve d.reserve_lt_one (normalSpace (I := IM) F₀ x)
    (normalSpace (I := IM) (d.map t u) x) (d.projection_gap t ht htt u hu x)
  have hbudget := originalC2PolarConstant_projection_bound A hA hcompact hcover F₀ hF₀ hi₀
    (d.map t u) (d.slice_smooth t u) (d.metric t ht htt u hu)
    (d.constant * t ^ ((44 : ℝ) / 5))
    (mul_nonneg d.constant_nonneg (Real.rpow_nonneg ht.le _))
    (d.closeness t ht htt u hu) x
  apply hlinear.trans
  simpa only [normalGapWithRate, gapRateConstant, abs_of_pos ht, mul_assoc] using
    mul_le_mul_of_nonneg_left hbudget
      (polarResponseConstantOn_nonneg d.reserve d.reserve_lt_one)

/-- A rate-bearing certificate for exactly the already constructed full
original probe, rather than a second probe with a different Q. -/
def chosenNormalGapWithRate [T2Space M]
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ChosenProbeNormalGap d.toExactProbeFamily where
  gap := d.normalGapWithRate
  gap_nonneg := d.normalGapWithRate_nonneg
  gap_tendsto := d.normalGapWithRate_tendsto
  gap_bound := fun t ht htt u hu _i x _hx ↦ d.normalGapWithRate_bound t ht htt u hu x

end NativeProbeData
end GlobalEmbedding.NormalPolar
