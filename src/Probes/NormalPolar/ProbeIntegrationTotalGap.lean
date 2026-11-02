import NormalPolar.MapFamily
import NormalPolar.ProbeIntegrationGap

/-!
# Same-Q gap for the total actual normal-identification field

The total normal identification preserves the supplied map at every parameter.
It is the explicit polar isometry whenever the two true projections are close,
and a rank-derived isometry elsewhere. Its same-Q gap follows from actual-map
C² budgets; no projection reserve or output estimate is assumed here.
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

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original actual maps and their quantitative first-jet/projection
budget produce a modulus for their actual total normal identification. No Q
is supplied, and no scale or parameter domain is reduced. -/
theorem exists_total_sameQ_gap_of_actual_projection_budget
    {P : Type*} (F₀ : M → V) (F : ℝ → P → M → V)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (T : Set ℝ) (U : Set P) (A : BufferedAtlas M E)
    (ε : ℝ → ℝ) (hε : ∀ t, 0 ≤ ε t)
    (hεlim : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hprojection : ∀ t ∈ T, ∀ u ∈ U, ∀ i z, z ∈ A.support i →
      ‖(normalSpace (I := IM) (F t u) z).starProjection -
        (normalSpace (I := IM) F₀ z).starProjection‖ ≤ ε t) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t ∈ T, ∀ u ∈ U, ∀ i z, z ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (F t u)
          (actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ ≤ g t := by
  obtain ⟨C, hC, hbound⟩ := exists_actualPolarOperator_gap_bound («V» := V)
  refine ⟨polarGapModulus C ε, polarGapModulus_nonneg C hC ε hε,
    polarGapModulus_tendsto C ε hεlim, ?_⟩
  intro t ht u hu i z hz
  by_cases hsmall : ε t ≤ (1 / 2 : ℝ)
  · have hp := hprojection t ht u hu i z hz
    have hclose : ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (F t u) z).starProjection‖ < 1 := by
      rw [norm_sub_rev]
      exact (hp.trans hsmall).trans_lt (by norm_num)
    rw [actualImmersionNormalIdentification_operator F₀ (F t u) hi₀ (hi t u) z hclose,
      polarGapModulus, ite_eq_left hsmall]
    exact hbound _ _ (normalSpace (I := IM) F₀ z).isIdempotentElem_starProjection
      (normalSpace (I := IM) F₀ z).starProjection_norm_le
      (normalSpace (I := IM) (F t u) z).starProjection_norm_le
      (ε t) (hε t) hsmall hp
  · rw [polarGapModulus, ite_eq_right hsmall]
    exact (norm_sub_le _ _).trans ((add_le_add
      (normalIdentificationOperator_norm_le_one F₀ (F t u)
        (actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)) z)
      (normalSpace (I := IM) F₀ z).starProjection_norm_le).trans_eq (by norm_num))

/-- A direct usable output before the rest of `ExactProbeFamily` exists.
Both the normal-identification field and its uniform same-Q gap are computed
from the same real maps and their original C² displacement budget. The input
immersion statements ensure the total field exists even outside the budget
domain; they do not assert any normal-isometry or output gap. -/
theorem exists_total_sameQ_gap_of_actual_maps_originalC2
    {P : Type*} (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : ℝ → P → M → V)
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (T : Set ℝ) (U : Set P)
    (hF : ∀ t ∈ T, ∀ u ∈ U, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hmetric : ∀ t ∈ T, ∀ u ∈ U, ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (b : ℝ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hblim : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbudget : ∀ t ∈ T, ∀ u ∈ U,
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (b t)) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t ∈ T, ∀ u ∈ U, ∀ i z, z ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (F t u)
          (actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ ≤ g t := by
  obtain ⟨K, hK, hproj⟩ :=
    exists_uniform_sameMetric_normalProjection_budget A hA hcompact F₀ hF₀ hi₀
  apply exists_total_sameQ_gap_of_actual_projection_budget F₀ F hi₀ hi T U A
    (fun t ↦ K * b t) (fun t ↦ mul_nonneg hK.le (hb t))
    (by simpa using hblim.const_mul K)
  intro t ht u hu i z hz
  exact hproj (F t u) (hF t ht u hu) (hmetric t ht u hu)
    (b t) (hb t) (hbudget t ht u hu) i z hz

/-- The original `ChosenProbeNormalGap` field for a probe using the actual
total construction. Only literal selection of this normal field is supplied;
all quantitative gap information is proved from the original probe fields.
In particular no separate projection gap or smallness reserve is required. -/
def chosenProbeNormalGapOfTotalCanonical
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (hselected : ∀ t ht htt u hu,
      probe.normalIdentification t u =
        actualImmersionNormalIdentification F₀ (probe.map t u) hi₀
          (fun x ↦ immersion_of_inducedMetric_eq F₀ (probe.map t u) x
            (probe.metric t ht htt u hu x) (hi₀ x))) :
    ChosenProbeNormalGap probe := by
  apply chosenProbeNormalGapOfOriginalC2 hA hcompact hi₀ probe
  intro t ht htt u hu i z hz hclose
  rw [hselected t ht htt u hu]
  apply actualImmersionNormalIdentification_operator
  simpa only [norm_sub_rev] using hclose

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_total_sameQ_gap_of_actual_projection_budget
#print axioms GlobalEmbedding.NormalPolar.exists_total_sameQ_gap_of_actual_maps_originalC2
#print axioms GlobalEmbedding.NormalPolar.chosenProbeNormalGapOfTotalCanonical
