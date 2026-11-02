import NormalPolar.GapReserve
import NormalPolar.MapFamily
import NormalPolar.ProbeIntegrationTotalGap

/-!
# One original-map input constructs the normal geometry and its same-Q gap

The reference constant is chosen from the reference immersion and fixed atlas
before the scale, parameter, and new map. All smallness inputs are original
C² budgets. The output has the supplied map, radius, and threshold unchanged.
No normal identification, its smoothness, or its gap is an input.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The constant is fixed by actual reference geometry, before the new map. -/
def originalC2PolarConstant
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) : ℝ :=
  (exists_originalC2_wholeSource_polar_reserve A hA hcompact hcover F₀ hF₀ hi₀).choose

theorem originalC2PolarConstant_pos
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    0 < originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ :=
  (exists_originalC2_wholeSource_polar_reserve A hA hcompact hcover F₀ hF₀ hi₀).choose_spec.1

/-- The original C² budget yields the real projection bound at every
source point. In particular a scalar bound `C * b ≤ q < 1` supplies the fixed
reserve used by the uniform parameter-response theorems. -/
theorem originalC2PolarConstant_projection_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b) (hbudget : probeAtlasCj A 2 (F - F₀) ≤ ENNReal.ofReal b) :
    ∀ x, ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ ≤
        originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b :=
  ((exists_originalC2_wholeSource_polar_reserve A hA hcompact hcover F₀ hF₀ hi₀).choose_spec.2
    F hF hmetric b hb hbudget).1

theorem originalC2PolarConstant_reserve
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hmetric : ∀ x, inducedMetric (I := IM) F x = inducedMetric (I := IM) F₀ x)
    (b : ℝ) (hb : 0 ≤ b) (hbudget : probeAtlasCj A 2 (F - F₀) ≤ ENNReal.ofReal b)
    (hsmall : originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b < 1) :
    ∀ x, ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < 1 :=
  ((exists_originalC2_wholeSource_polar_reserve A hA hcompact hcover F₀ hF₀ hi₀).choose_spec.2
    F hF hmetric b hb hbudget).2 hsmall

/-- Identity extension outside the admitted domain makes every actual
slice an immersion. On the domain this follows from the real metric equality.
This theorem does not extend, replace, or otherwise modify the supplied map. -/
theorem actualFamily_immersion_of_sameMetric_and_identityOutside
    (F₀ : M → V) (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (F : ℝ → ProbeParameters r → M → V) (radius threshold : ℝ)
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (houtside : ∀ t u, ¬ (0 < t ∧ t < threshold ∧ ‖u‖ < radius) → F t u = F₀) :
    ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x) := by
  intro t u x
  by_cases ha : 0 < t ∧ t < threshold ∧ ‖u‖ < radius
  · exact immersion_of_inducedMetric_eq F₀ (F t u) x
      (hmetric t ha.1 ha.2.1 u ha.2.2 x) (hi₀ x)
  · rw [houtside t u ha]
    exact hi₀ x

/-- A direct original-interface constructor from actual maps and original
C² budgets. The original radius and threshold are preserved literally.
`hi` is a fact about the supplied maps, and can be discharged by the preceding
identity-outside theorem when the upstream family uses that extension. -/
def probeGeometryOfOriginalC2
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (F : ℝ → ProbeParameters r → M → V)
    (radius threshold : ℝ) (hradius : 0 < radius) (hthreshold : 0 < threshold)
    (hF : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hbudget : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (b t))
    (hsmall : ∀ t, 0 < t → t < threshold →
      originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b t < 1) :
    ProbeGeometry (n := n) F₀ r :=
  probeGeometryOfActualImmersions F₀ hF₀ hi₀ F radius threshold hradius hthreshold
    hF hi hjoint hmetric (fun t ht htt u hu ↦
      originalC2PolarConstant_reserve A hA hcompact hcover F₀ hF₀ hi₀
        (F t u) (hF t u) (hmetric t ht htt u hu) (b t) (hb t)
        (hbudget t ht htt u hu) (hsmall t ht htt))

/-- The very same constructed geometry has the required uniform same-Q
gap before the remaining fields of ExactProbeFamily exist. -/
theorem probeGeometryOfOriginalC2_sameQ_gap
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (F : ℝ → ProbeParameters r → M → V)
    (radius threshold : ℝ) (hradius : 0 < radius) (hthreshold : 0 < threshold)
    (hF : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hblim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (b t))
    (hsmall : ∀ t, 0 < t → t < threshold →
      originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b t < 1) :
    let geometry := probeGeometryOfOriginalC2 A hA hcompact hcover F₀ hF₀ hi₀
      F radius threshold hradius hthreshold hF hi hjoint hmetric b hb hbudget hsmall
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
      ∀ i z, z ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (geometry.map t u)
          (geometry.normalIdentification t u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ ≤ g t := by
  obtain ⟨g, hg, hlim, hbound⟩ := exists_total_sameQ_gap_of_actual_maps_originalC2
    F₀ hF₀ hi₀ F hi (Set.Ioo 0 threshold) (Metric.ball 0 radius)
    (fun t _ u _ ↦ hF t u) A hA hcompact
    (fun t ht u hu ↦ hmetric t ht.1 ht.2 u (by simpa using hu)) b hb hblim
    (fun t ht u hu ↦ hbudget t ht.1 ht.2 u (by simpa using hu))
  refine ⟨g, hg, hlim, ?_⟩
  intro t ht htt u hu i z hz
  exact hbound t ⟨ht, htt⟩ u (by simpa using hu) i z hz

end GlobalEmbedding.NormalPolar
