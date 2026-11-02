import NormalPolar.GapProjection

/-!
# A whole-source polar reserve from the original C² budget

The cover is used only to pass from the original support estimates to every
source point. The reserve constant is chosen from reference geometry before
the new map, its scale and its parameter. No alternative parameter ball or
new source atlas is selected.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A uniform true first-jet/projection reserve, valid on the whole source.
The only smallness assumption is the actual original C² displacement budget
times a constant computed from the reference immersion. -/
theorem exists_originalC2_wholeSource_polar_reserve
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ F →
      (∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x) →
      ∀ b : ℝ, 0 ≤ b → probeAtlasCj A 2 (F - F₀) ≤ ENNReal.ofReal b →
      (∀ x, ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ ≤ C * b) ∧
      (C * b < 1 → ∀ x, ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ < 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_sameMetric_normalProjection_budget A hA hcompact F₀ hF₀ himm
  refine ⟨C, hC, ?_⟩
  intro F hF hmetric b hb hbudget
  have hglobal (x : M) : ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ ≤ C * b := by
    obtain ⟨i, hx⟩ := hcover x
    rw [norm_sub_rev]
    exact hbound F hF hmetric b hb hbudget i x hx
  exact ⟨hglobal, fun hsmall x ↦ (hglobal x).trans_lt hsmall⟩

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_originalC2_wholeSource_polar_reserve
