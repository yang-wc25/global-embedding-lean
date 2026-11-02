import NormalPolar.ResponseUniform
import Upgrade.IncidenceAtlasLeading
import Upgrade.SupportedHessianC3
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Actual quantitative inputs for the full identified second-form response

The wave bound uses the genuine tensor in the original inverse chart frame.
The Hessian bound comes from the original atlas C³ norm.  No second-form or
normal-identification response is assumed.  The scalar modulus preserves the
original exponents and is nonnegative for all real scale arguments.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

theorem probeTrig_abs_le_one (b : Bool) (theta : ℝ) :
    |probeTrig b theta| ≤ 1 := by
  cases b
  · exact Real.abs_cos_le_one theta
  · exact Real.abs_sin_le_one theta

theorem norm_probe_single_direction_le_one {r : ℕ} (l : Fin r) (b : Bool) :
    ‖(Pi.single (l, b) 1 : ProbeParameters r)‖ ≤ 1 := by
  rw [Pi.norm_single]
  norm_num

/-- The actual ratio between the first-jet response scale and the leading
second-form scale, without restricting or shrinking the original t-domain. -/
theorem probe_ten_scale_eq_sigma_mul (t : ℝ) (ht : 0 < t) :
    t ^ (10 : ℕ) = t ^ ((44 : ℝ) / 5) * |t| ^ ((6 : ℝ) / 5) := by
  rw [abs_of_pos ht, ← Real.rpow_add ht]
  norm_num

/-- A global nonnegative extension of the genuine small-scale response
modulus. On positive scales the absolute value has no effect. -/
def fullSecondFormModulus (L B D : ℝ) (etaH gap : ℝ → ℝ) (t : ℝ) : ℝ :=
  L * etaH t + B * gap t + D * |t| ^ ((6 : ℝ) / 5)

theorem fullSecondFormModulus_nonneg (L B D : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (etaH gap : ℝ → ℝ) (hetaH : ∀ t, 0 ≤ etaH t) (hgap : ∀ t, 0 ≤ gap t)
    (t : ℝ) : 0 ≤ fullSecondFormModulus L B D etaH gap t := by
  unfold fullSecondFormModulus
  exact add_nonneg (add_nonneg (mul_nonneg hL (hetaH t)) (mul_nonneg hB (hgap t)))
    (mul_nonneg hD (Real.rpow_nonneg (abs_nonneg t) _))

theorem fullSecondFormModulus_tendsto (L B D : ℝ) (etaH gap : ℝ → ℝ)
    (hetaH : Tendsto etaH (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgap : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fullSecondFormModulus L B D etaH gap) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Continuous (fun t : ℝ ↦ |t| ^ ((6 : ℝ) / 5)) :=
    (Real.continuous_rpow_const (by norm_num : 0 ≤ (6 : ℝ) / 5)).comp continuous_abs
  have hp0 : Tendsto (fun t : ℝ ↦ |t| ^ ((6 : ℝ) / 5))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hp.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  unfold fullSecondFormModulus
  simpa only [mul_zero, add_zero] using
    ((hetaH.const_mul L).add (hgap.const_mul B)).add (hp0.const_mul D)

theorem fullSecondFormModulus_scaled (L B D C v : ℝ) (etaH gap : ℝ → ℝ)
    (t : ℝ) (ht : 0 < t) :
    L * (t ^ ((44 : ℝ) / 5) * (etaH t + C * v)) +
        gap t * (t ^ ((44 : ℝ) / 5) * B) + D * t ^ (10 : ℕ) =
      t ^ ((44 : ℝ) / 5) *
        (fullSecondFormModulus L B D etaH gap t + (L * C) * v) := by
  rw [probe_ten_scale_eq_sigma_mul t ht]
  unfold fullSecondFormModulus
  ring

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The current actual descended Hessian is bounded by the original C³
budget, at the same original chart supports. -/
theorem probeAtlasSecondJet_norm_le_originalC3
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (C : ℝ) (hC : 0 ≤ C) (hbound : probeAtlasCj A 3 F ≤ ENNReal.ofReal C)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖probeAtlasSecondJet A F i x‖ ≤
      actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * C) := by
  apply (coordinateHessianJet_norm_le_native_second (F ∘ (A.chart i).symm)
    (A.chart i x)).trans
  exact mul_le_mul_of_nonneg_left
    (probeAtlas_native_derivative_bound A hA F hF hC hbound (by norm_num : 2 ≤ 3) i x hx)
    actualHessianLiftConstant_nonneg

/-- One finite reference constant bounds every actual leading wave tensor
in every original inverse chart frame on its compact support. -/
theorem exists_uniform_wave_tensor_in_frame_bound [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {r : ℕ} (waves : Fin r → LocalLegalWave F₀ hF₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ l i x, x ∈ A.support i →
      ‖probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤ B := by
  have hc (l : Fin r) (i : Fin A.count) : ContinuousOn
      (fun x ↦ probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x))
      (A.support i) := by
    have hcoord := ((waves l).atlasLeadingTensor_contDiffOn A hA i).continuousOn.comp
      (A.chart i).continuousOn (fun x hx ↦ (A.chart i).map_source hx)
    have hsource : ContinuousOn
        (fun x ↦ probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x))
        (A.chart i).source := by
      apply hcoord.congr
      intro x hx
      symm
      simpa only [Function.comp_apply, (A.chart i).left_inv hx] using
        (waves l).atlasLeadingTensor_eq A hA i (A.chart i x) ((A.chart i).map_source hx)
    exact hsource.mono (hA.support_subset i)
  choose B hB using fun k : Fin r × Fin A.count ↦
    (hcompact k.2).exists_bound_of_continuousOn (hc k.1 k.2)
  obtain ⟨K, hK⟩ := Finite.exists_le B
  refine ⟨|K| + 1, by positivity, ?_⟩
  intro l i x hx
  exact (hB (l, i) x hx).trans ((hK (l, i)).trans ((le_abs_self K).trans (by linarith)))

end GlobalEmbedding.NormalPolar
