import NormalPolar.IdentificationTransportReselection

/-!
# Actual operator budgets for identification transport

Separate bounds for the two actual operators imply the change control.
The gauge derivative bound remains a theorem from the earlier modules.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The old actual identification may have unrelated parameter rotations.
These are precisely the extra old-Q budgets needed by the norm-based
transport estimate. They do not follow from the old full response alone. -/
structure OldNormalIdentificationControl
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves) where
  gap : ℝ → ℝ
  derivative : ℝ → ℝ
  gap_nonneg : ∀ t, 0 ≤ gap t
  derivative_nonneg : ∀ t, 0 ≤ derivative t
  gap_tendsto : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0)
  derivative_tendsto : Tendsto derivative (𝓝[>] (0 : ℝ)) (𝓝 0)
  gap_bound : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
    ∀ i x, x ∈ A.support i →
      ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x -
        (normalSpace (I := IM) F₀ x).starProjection‖ ≤ gap t
  derivative_bound : ∀ t, 0 < t → t < p.threshold → ∀ u d, ‖u‖ < p.radius →
    ∀ i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v)
        (p.normalIdentification t v) x) u d‖ ≤
          t ^ ((44 : ℝ) / 5) * derivative t * ‖d‖

/-- Actual old and new projection-relative budgets give the change
control by a proved triangle inequality. -/
def normalIdentificationChangeControlOfSeparateBudgets
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (old : OldNormalIdentificationControl p)
    (gap derivative : ℝ → ℝ)
    (hgap : ∀ t, 0 ≤ gap t) (hderivative : ∀ t, 0 ≤ derivative t)
    (hgaplim : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hderivativelim : Tendsto derivative (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgapbound : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
      ∀ i x, x ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (p.map t u) (Q t u) x -
          (normalSpace (I := IM) F₀ x).starProjection‖ ≤ gap t)
    (hderivativebound : ∀ t, 0 < t → t < p.threshold → ∀ u d, ‖u‖ < p.radius →
      ∀ i x, x ∈ A.support i →
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v) (Q t v) x) u d‖ ≤
          t ^ ((44 : ℝ) / 5) * derivative t * ‖d‖) :
    NormalIdentificationChangeControl p Q where
  gap := fun t ↦ gap t + old.gap t
  derivative := fun t ↦ derivative t + old.derivative t
  gap_nonneg := fun t ↦ add_nonneg (hgap t) (old.gap_nonneg t)
  derivative_nonneg := fun t ↦ add_nonneg (hderivative t) (old.derivative_nonneg t)
  gap_tendsto := by simpa only [add_zero] using hgaplim.add old.gap_tendsto
  derivative_tendsto := by simpa only [add_zero] using hderivativelim.add old.derivative_tendsto
  gap_bound := by
    intro t ht htt u hu i x hx
    let Qn := normalIdentificationOperator (n := n) F₀ (p.map t u) (Q t u) x
    let Qo := normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) x
    let P₀ := (normalSpace (I := IM) F₀ x).starProjection
    have heq : Qn - Qo = (Qn - P₀) - (Qo - P₀) := by abel
    calc
      ‖Qn - Qo‖ = ‖(Qn - P₀) - (Qo - P₀)‖ := congrArg norm heq
      _ ≤ ‖Qn - P₀‖ + ‖Qo - P₀‖ := norm_sub_le _ _
      _ ≤ gap t + old.gap t :=
        add_le_add (hgapbound t ht htt u hu i x hx) (old.gap_bound t ht htt u hu i x hx)
  derivative_bound := by
    intro t ht htt u d hu i x hx
    calc
      _ ≤ t ^ ((44 : ℝ) / 5) * derivative t * ‖d‖ +
          t ^ ((44 : ℝ) / 5) * old.derivative t * ‖d‖ :=
        add_le_add (hderivativebound t ht htt u d hu i x hx)
          (old.derivative_bound t ht htt u d hu i x hx)
      _ = _ := by ring

end GlobalEmbedding.NormalPolar
