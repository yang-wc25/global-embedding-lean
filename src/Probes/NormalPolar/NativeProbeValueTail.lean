import NormalPolar.NativeProbeData
import Upgrade.CompactProbeAtlas

/-!
# Actual value-response tails in the original atlas norm

An original C⁰ (or stronger Cʲ) budget for the actual parameter response of a
correction controls its value at every source point. Joint smoothness of the
two actual families proves derivative subtraction on the same open parameter
domain. These lemmas transfer an already proved leading response from a
preliminary map to the actual final map without constructing or assuming the
existence of any correction.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

/-- The genuine target-coordinate conversion in the original atlas Cʲ norm.
Its definition covers zero-dimensional targets. -/
def nativeValueTailConstant (N : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖

theorem nativeValueTailConstant_nonneg (N : ℕ) : 0 ≤ nativeValueTailConstant N :=
  norm_nonneg _

/-- The model modulus plus the actual value-tail contribution. -/
def nativeValueTailModulus (N : ℕ) (etaModel etaTail : ℝ → ℝ) (t : ℝ) : ℝ :=
  etaModel t + nativeValueTailConstant N * etaTail t

theorem nativeValueTailModulus_nonneg (N : ℕ) (etaModel etaTail : ℝ → ℝ)
    (hModel : ∀ t, 0 ≤ etaModel t) (hTail : ∀ t, 0 ≤ etaTail t) (t : ℝ) :
    0 ≤ nativeValueTailModulus N etaModel etaTail t :=
  add_nonneg (hModel t) (mul_nonneg (nativeValueTailConstant_nonneg N) (hTail t))

theorem nativeValueTailModulus_tendsto (N : ℕ) (etaModel etaTail : ℝ → ℝ)
    (hModel : Tendsto etaModel (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hTail : Tendsto etaTail (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (nativeValueTailModulus N etaModel etaTail) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  change Tendsto (fun t ↦ etaModel t + nativeValueTailConstant N * etaTail t)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero, add_zero] using
    hModel.add (hTail.const_mul (nativeValueTailConstant N))

variable {n N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- Actual value responses are differentiable on the given open parameter
domain because the supplied actual family is jointly smooth. -/
theorem actual_parameter_value_differentiableAt_of_joint
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {U : Set P} (hU : IsOpen U) (F : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (u : P) (hu : u ∈ U) (x : M) :
    DifferentiableAt ℝ (fun v ↦ F v x) u := by
  obtain ⟨i, hxi⟩ := hcover x
  have hx := hA.support_subset i hxi
  have hf := contDiffOn_actual_parameter_atlas_pullback A hA i (Function.uncurry F) hF
  have hopen := hU.prod (A.chart i).open_target
  have hw : (u, A.chart i x) ∈ U ×ˢ (A.chart i).target :=
    ⟨hu, (A.chart i).map_source hx⟩
  have h := actual_parameter_differentiableAt _
    ((hf.contDiffAt (hopen.mem_nhds hw)).differentiableAt (by simp))
  simpa only [Function.uncurry_apply_pair, (A.chart i).left_inv hx] using h

/-- Differentiate the actual correction F-G; no separately chosen response
field is substituted for its native derivative. -/
theorem actual_parameter_value_response_sub
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) :
    fderiv ℝ (fun v ↦ F v x - G v x) u d =
      fderiv ℝ (fun v ↦ F v x) u d - fderiv ℝ (fun v ↦ G v x) u d := by
  have heq : (fun v ↦ F v x - G v x) = (fun v ↦ F v x) - (fun v ↦ G v x) := by
    funext v
    rfl
  rw [heq, fderiv_sub
    (actual_parameter_value_differentiableAt_of_joint A hA hcover hU F hF u hu x)
    (actual_parameter_value_differentiableAt_of_joint A hA hcover hU G hG u hu x)]
  rfl

/-- An original Cʲ bound on the actual response difference transfers a
leading value term, uniformly at every source point. The order-zero part is
enough, and no differentiability of this response field is required. -/
theorem actual_value_response_bound_of_originalCj_tail
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (j : ℕ)
    (F G : P → M → V) (u d : P) (x : M) (L : V)
    {e b : ℝ} (hb : 0 ≤ b)
    (hmodel : ‖fderiv ℝ (fun v ↦ G v x) u d - L‖ ≤ e)
    (htail : probeAtlasCj A j
      (fun y ↦ fderiv ℝ (fun v ↦ F v y) u d -
        fderiv ℝ (fun v ↦ G v y) u d) ≤ ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ F v x) u d - L‖ ≤ e + nativeValueTailConstant N * b := by
  have hdiff := norm_le_of_probeAtlasCj A hA hcover j _ hb htail x
  let DF := fderiv ℝ (fun v ↦ F v x) u d
  let DG := fderiv ℝ (fun v ↦ G v x) u d
  calc
    _ = ‖(DF - DG) + (DG - L)‖ := by congr 1; dsimp only [DF, DG]; abel
    _ ≤ ‖DF - DG‖ + ‖DG - L‖ := norm_add_le (DF - DG) (DG - L)
    _ ≤ nativeValueTailConstant N * b + e := add_le_add hdiff hmodel
    _ = _ := add_comm _ _

/-- The same transfer with a budget literally on the native derivative of
the actual correction, using joint smoothness only to prove subtraction. -/
theorem actual_value_response_bound_of_originalCj_correction
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (j : ℕ)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (L : V)
    {e b : ℝ} (hb : 0 ≤ b)
    (hmodel : ‖fderiv ℝ (fun v ↦ G v x) u d - L‖ ≤ e)
    (htail : probeAtlasCj A j
      (fun y ↦ fderiv ℝ (fun v ↦ F v y - G v y) u d) ≤ ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ F v x) u d - L‖ ≤ e + nativeValueTailConstant N * b := by
  apply actual_value_response_bound_of_originalCj_tail A hA hcover j F G u d x L hb hmodel
  simpa only [actual_parameter_value_response_sub A hA hcover hU F G hF hG u d hu] using htail

/-- Exact factorization at any nonnegative amplitude. In particular the
original value amplitude t^(56/5) is used without changing t or its domain. -/
theorem actual_value_response_scaled_bound_of_originalCj_correction
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (j : ℕ)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (L : V)
    (amplitude etaModel etaTail CModel CTail : ℝ)
    (hamp : 0 ≤ amplitude) (hetaTail : 0 ≤ etaTail) (hCTail : 0 ≤ CTail)
    (hmodel : ‖fderiv ℝ (fun v ↦ G v x) u d - L‖ ≤
      amplitude * (etaModel + CModel * ‖u‖))
    (htail : probeAtlasCj A j
      (fun y ↦ fderiv ℝ (fun v ↦ F v y - G v y) u d) ≤
        ENNReal.ofReal (amplitude * (etaTail + CTail * ‖u‖))) :
    ‖fderiv ℝ (fun v ↦ F v x) u d - L‖ ≤
      amplitude * ((etaModel + nativeValueTailConstant N * etaTail) +
        (CModel + nativeValueTailConstant N * CTail) * ‖u‖) := by
  have h := actual_value_response_bound_of_originalCj_correction A hA hcover j hU F G hF hG
    u d hu x L (mul_nonneg hamp (add_nonneg hetaTail (mul_nonneg hCTail (norm_nonneg u))))
    hmodel htail
  convert h using 1
  ring

end GlobalEmbedding.NormalPolar
