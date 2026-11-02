import NormalPolar.IdentificationTransportBounds

/-!
# A complete ExactProbeFamily after a justified change of actual Q

The old quantitative record alone does not control the derivative of an
arbitrary old normal identification.  The actual extra operator budgets are
therefore explicit in `NormalIdentificationChangeControl`.  The constructor
below proves the new response using them, while keeping the same actual map,
parameter ball, threshold, weights and all other original quantitative data.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Genuine operator control sufficient to transport the old full response.
The derivative is that of the two actual Qops; neither a gauge derivative
nor a second-form response identity is assumed here. -/
structure NormalIdentificationChangeControl
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z) where
  gap : ℝ → ℝ
  derivative : ℝ → ℝ
  gap_nonneg : ∀ t, 0 ≤ gap t
  derivative_nonneg : ∀ t, 0 ≤ derivative t
  gap_tendsto : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0)
  derivative_tendsto : Tendsto derivative (𝓝[>] (0 : ℝ)) (𝓝 0)
  gap_bound : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
    ∀ i x, x ∈ A.support i →
      ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (Q t u) x -
        normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x‖ ≤ gap t
  derivative_bound : ∀ t, 0 < t → t < p.threshold → ∀ u d, ‖u‖ < p.radius →
    ∀ i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v) (Q t v) x) u d‖ +
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v)
          (p.normalIdentification t v) x) u d‖ ≤
            t ^ ((44 : ℝ) / 5) * derivative t * ‖d‖

/-- A full probe record using the new actual Q. The second-form response
is rebuilt by the proved transport formula, with its complete new modulus. -/
def exactProbeFamilyWithNormalIdentification [T2Space M]
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hQ : ∀ t, 0 < t → t < p.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (p.map t w.1) (Q t w.1) w.2) (Metric.ball 0 p.radius ×ˢ univ))
    (control : NormalIdentificationChangeControl p Q) :
    ExactProbeFamily F₀ hF₀ A waves := by
  let hex := exists_uniform_wave_tensor_in_frame_bound A hA hcompact waves
  let B := Classical.choose hex
  have hB : 0 < B := (Classical.choose_spec hex).1
  have hBbound := (Classical.choose_spec hex).2
  let H := actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * p.constant)
  have hH : 0 ≤ H := mul_nonneg actualHessianLiftConstant_nonneg
    (mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 2) p.constant_nonneg)
  exact { p with
    normalIdentification := Q
    normalIdentification_smooth := hQ
    etaB := transportedSecondFormModulus B H p.etaB control.gap control.derivative
    etaB_nonneg := transportedSecondFormModulus_nonneg B H hB.le hH
      p.etaB control.gap control.derivative p.etaB_nonneg
      control.gap_nonneg control.derivative_nonneg
    etaB_tendsto := transportedSecondFormModulus_tendsto B H
      p.etaB control.gap control.derivative p.etaB_tendsto
      control.gap_tendsto control.derivative_tendsto
    secondForm_response := exactProbeFamily_secondForm_response_transport hA p Q hQ B hBbound
      control.gap control.derivative control.gap_nonneg control.derivative_nonneg
      control.gap_bound control.derivative_bound }

/-- The reselection retains every non-Q field relevant to the original
probe construction. These equalities include the entire original domain. -/
theorem exactProbeFamilyWithNormalIdentification_preserves [T2Space M]
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hQ : ∀ t, 0 < t → t < p.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (p.map t w.1) (Q t w.1) w.2) (Metric.ball 0 p.radius ×ˢ univ))
    (control : NormalIdentificationChangeControl p Q) :
    let pnew := exactProbeFamilyWithNormalIdentification hA hcompact p Q hQ control
    pnew.map = p.map ∧ pnew.radius = p.radius ∧ pnew.threshold = p.threshold ∧
      pnew.weight = p.weight ∧ pnew.constant = p.constant ∧ pnew.etaV = p.etaV ∧
      pnew.normalIdentification = Q := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalEmbedding.NormalPolar
