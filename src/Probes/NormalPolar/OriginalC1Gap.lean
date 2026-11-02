import NormalPolar.NativeProbeExplicitResponse

/-!
# Same-Q projection input from the actual spatial C¹ displacement

The original zero-order normal gap only uses first jets of the actual map.
This file derives their genuine difference from the original spatial C¹ norm,
then reuses the fixed-reference constant already chosen for native responses.
The spatial displacement budget is distinct from a parameter-response budget.
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

/-- The literal first jets of two actual smooth maps are controlled by their
original spatial C¹ displacement. No second-jet or projection budget is input. -/
theorem probeAtlas_firstJet_difference_originalC1
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : probeAtlasCj A 1 (G - F) ≤ ENNReal.ofReal b)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x‖ ≤
      probeAtlasDerivativeConstant n N 1 * b := by
  have hxT := (A.chart i).map_source (hA.support_subset i hx)
  have hFc : ContDiffAt ℝ 1 (F ∘ (A.chart i).symm) (A.chart i x) :=
    ((probeAtlas_fixed_coordinate_smooth A hA F hF i).contDiffAt
      ((A.chart i).open_target.mem_nhds hxT)).of_le (by simp)
  have hGc : ContDiffAt ℝ 1 (G ∘ (A.chart i).symm) (A.chart i x) :=
    ((probeAtlas_fixed_coordinate_smooth A hA G hG i).contDiffAt
      ((A.chart i).open_target.mem_nhds hxT)).of_le (by simp)
  have heq : probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x =
      fderiv ℝ ((G - F) ∘ (A.chart i).symm) (A.chart i x) :=
    (fderiv_sub (hGc.differentiableAt (by simp))
      (hFc.differentiableAt (by simp))).symm
  rw [heq, ← norm_iteratedFDeriv_one]
  exact probeAtlas_native_derivative_bound A hA (G - F) (hG.sub hF)
    hb hbound (show 1 ≤ 1 by rfl) i x hx

/-- The reference constant is fixed before the later map and its actual C¹
budget. The two normal projections are the genuine ones of these maps. -/
theorem sameMetric_normalProjection_gap_originalC1_on_support
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : probeAtlasCj A 1 (F - F₀) ≤ ENNReal.ofReal b)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ ≤
      nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ * b := by
  let c := 2 * ‖((probeAtlasFirstJet A F₀ i x).adjoint.comp
    (probeAtlasFirstJet A F₀ i x)).inverse‖ * ‖probeAtlasFirstJet A F₀ i x‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp := trueNormalProjection_gap_of_sameMetric_firstJet A hA F₀ F hF₀ hF
    i x (hA.support_subset i hx) (hi₀ x) (hmetric x)
  have hj := probeAtlas_firstJet_difference_originalC1 A hA F₀ F hF₀ hF hb hbound i x hx
  calc
    _ = ‖(normalSpace (I := IM) F x).starProjection -
        (normalSpace (I := IM) F₀ x).starProjection‖ := norm_sub_rev _ _
    _ ≤ c * ‖probeAtlasFirstJet A F i x - probeAtlasFirstJet A F₀ i x‖ := hp
    _ ≤ c * (probeAtlasDerivativeConstant n N 1 * b) := mul_le_mul_of_nonneg_left hj hc
    _ = (c * probeAtlasDerivativeConstant n N 1) * b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (nativeReferenceResponseFactor_bound A hA hcompact F₀ hF₀ hi₀ i x hx) hb

/-- An actual support cover promotes the same first-jet bound to every
source point, including disconnected or empty sources. -/
theorem sameMetric_normalProjection_gap_originalC1
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : probeAtlasCj A 1 (F - F₀) ≤ ENNReal.ofReal b) (x : M) :
    ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ ≤
      nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ * b := by
  obtain ⟨i, hx⟩ := hcover x
  exact sameMetric_normalProjection_gap_originalC1_on_support A hA hcompact F₀ hF₀ hi₀
    F hF hmetric b hb hbound i x hx

end GlobalEmbedding.NormalPolar
