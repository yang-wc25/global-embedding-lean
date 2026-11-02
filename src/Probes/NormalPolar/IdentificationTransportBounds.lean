import NormalPolar.IdentificationTransportProbe
import NormalPolar.FullResponseBounds

/-!
# Quantitative response transport with the original probe budgets

The current identified form is bounded by the original C³ budget, using
the actual Hessian formula and the contraction of the actual identification.
The transported modulus keeps the old response error, the actual change of
identification and the actual derivative of both identifications.  No new
response statement is taken as an input.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- A modulus for replacing an actual identification. `derivative` measures
the true two-identification derivative budget after division by the original
second-form scale. -/
def transportedSecondFormModulus (B H : ℝ)
    (oldError gap derivative : ℝ → ℝ) (t : ℝ) : ℝ :=
  oldError t + B * gap t + H * derivative t

theorem transportedSecondFormModulus_nonneg (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (oldError gap derivative : ℝ → ℝ)
    (hold : ∀ t, 0 ≤ oldError t) (hgap : ∀ t, 0 ≤ gap t)
    (hderivative : ∀ t, 0 ≤ derivative t) (t : ℝ) :
    0 ≤ transportedSecondFormModulus B H oldError gap derivative t := by
  exact add_nonneg (add_nonneg (hold t) (mul_nonneg hB (hgap t)))
    (mul_nonneg hH (hderivative t))

theorem transportedSecondFormModulus_tendsto (B H : ℝ)
    (oldError gap derivative : ℝ → ℝ)
    (hold : Tendsto oldError (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgap : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hderivative : Tendsto derivative (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (transportedSecondFormModulus B H oldError gap derivative)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  unfold transportedSecondFormModulus
  simpa only [mul_zero, add_zero] using
    (hold.add (hgap.const_mul B)).add (hderivative.const_mul H)

theorem transportedSecondFormModulus_scaled (B H C sigma v : ℝ)
    (oldError gap derivative : ℝ → ℝ) (t : ℝ) :
    sigma * (oldError t + C * v) + gap t * (sigma * B) +
        (sigma * derivative t) * H =
      sigma * (transportedSecondFormModulus B H oldError gap derivative t + C * v) := by
  unfold transportedSecondFormModulus
  ring

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The current actual identified form has a uniform bound from the
original C³ norm; this is independent of which actual orthogonal Q is used. -/
theorem identifiedTrueSecondForm_in_frame_norm_le_originalC3
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (C : ℝ) (hC : 0 ≤ C) (hbound : probeAtlasCj A 3 F ≤ ENNReal.ofReal C)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖probeTensorInFrame (probeAtlasFrame A i x)
        (identifiedTrueSecondForm (n := n) F₀ F hF Q x)‖ ≤
      actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * C) := by
  rw [identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ F hF Q
    A hA i x (hA.support_subset i hx)]
  calc
    _ ≤ ‖normalIdentificationOperator (n := n) F₀ F Q x‖ *
        ‖probeAtlasSecondJet A F i x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * C)) :=
      mul_le_mul (normalIdentificationOperator_norm_le_one F₀ F Q x)
        (probeAtlasSecondJet_norm_le_originalC3 A hA F hF C hC hbound i x hx)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The original second-form response transported to a new actual Q on
the same maps and admitted domain. The two extra hypotheses are genuine
operator budgets, not a response of the identified form or of the gauge. -/
theorem exactProbeFamily_secondForm_response_transport
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hQ : ∀ t, 0 < t → t < p.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (p.map t w.1) (Q t w.1) w.2) (Metric.ball 0 p.radius ×ˢ univ))
    (B : ℝ)
    (hBbound : ∀ l i x, x ∈ A.support i →
      ‖probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤ B)
    (gap derivative : ℝ → ℝ) (hgap : ∀ t, 0 ≤ gap t)
    (hderivative : ∀ t, 0 ≤ derivative t)
    (hgapbound : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
      ∀ i x, x ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (Q t u) x -
          normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x‖ ≤ gap t)
    (hderivativebound : ∀ t, 0 < t → t < p.threshold → ∀ u d, ‖u‖ < p.radius →
      ∀ i x, x ∈ A.support i →
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v) (Q t v) x) u d‖ +
          ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v)
            (p.normalIdentification t v) x) u d‖ ≤
              t ^ ((44 : ℝ) / 5) * derivative t * ‖d‖)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i x)
        (identifiedTrueSecondForm (n := n) F₀ (p.map t v) (p.slice_smooth t v) (Q t v) x))
        u (Pi.single (l, b) 1) -
      (t ^ ((44 : ℝ) / 5) * probeTrig b (p.weight l * (waves l).phase x /
        t ^ ((6 : ℝ) / 5))) •
          probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤
      t ^ ((44 : ℝ) / 5) *
        (transportedSecondFormModulus B
          (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * p.constant))
          p.etaB gap derivative t + p.constant * ‖u‖) := by
  let sigma := t ^ ((44 : ℝ) / 5)
  let theta := p.weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5)
  let coefficient := sigma * probeTrig b theta
  have hsigma : 0 ≤ sigma := Real.rpow_nonneg ht.le _
  have hc : ‖coefficient‖ ≤ sigma := by
    dsimp only [coefficient]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsigma]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (probeTrig_abs_le_one b theta) hsigma
  have hprincipal :
      ‖coefficient • probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤ sigma * B := by
    rw [norm_smul]
    exact mul_le_mul hc (hBbound l i x hx) (norm_nonneg _) hsigma
  have hd := hderivativebound t ht htt u (Pi.single (l, b) 1) hu i x hx
  simp only [Pi.norm_single, norm_one, mul_one] at hd
  have hform := identifiedTrueSecondForm_in_frame_norm_le_originalC3 A hA F₀ (p.map t u)
    (p.slice_smooth t u) (p.normalIdentification t u) p.constant p.constant_nonneg
    (p.spatial_C3 t ht htt u hu) i x hx
  have htransport := probeGeometry_secondForm_response_transport p.toProbeGeometry Q hQ (waves l)
    A hA i t ht htt u (Pi.single (l, b) 1) hu x (hA.support_subset i hx) coefficient
  have hbound := htransport.trans (add_le_add (add_le_add
    (p.secondForm_response t ht htt u hu l b i x hx)
    (mul_le_mul (hgapbound t ht htt u hu i x hx) hprincipal (norm_nonneg _) (hgap t)))
    (mul_le_mul hd hform (norm_nonneg _) (mul_nonneg hsigma (hderivative t))))
  exact hbound.trans_eq (transportedSecondFormModulus_scaled B
    (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * p.constant))
    p.constant sigma ‖u‖ p.etaB gap derivative t)

end GlobalEmbedding.NormalPolar
