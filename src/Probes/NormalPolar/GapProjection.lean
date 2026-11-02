import Round2.MetricLeftInverseCompact
import Probes.ActualFixedMetricNormalProjection

/-!
# The true normal-projection budget on the original atlas

The constant below is selected from the reference immersion and the original
compact atlas supports.  Every later smooth map with the same induced metric
inherits this bound from its original C² displacement budget.  In particular,
there is no separately supplied normal projection, selected identification, or
normal-identification estimate in the hypotheses.
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

/-- Actual fixed-metric first jets give the true projection gap in the same
fixed source chart. No normal-frame trivialization is chosen. -/
theorem trueNormalProjection_gap_of_sameMetric_firstJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hmetric : inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) :
    ‖(normalSpace (I := IM) G x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ ≤
      (2 * ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖) *
          ‖probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x‖ := by
  have himmG := immersion_of_inducedMetric_eq F G x hmetric himm
  have hjetF := probeAtlasFirstJet_injective A hA F hF i x hx himm
  have hjetG := probeAtlasFirstJet_injective A hA G hG i x hx himmG
  have hgram := probeAtlasFirstJet_gram_eq_of_inducedMetric_eq A hA F G hF hG i x hx hmetric
  have hnorm := probeAtlasFirstJet_norm_eq_of_inducedMetric_eq A hA F G hF hG i x hx hmetric
  rw [normalSpace_eq_probeAtlasFirstJet_range A hA G hG i x hx,
    normalSpace_eq_probeAtlasFirstJet_range A hA F hF i x hx]
  have h := norm_actualNormalProjection_sub_fixed_metric_le
    (probeAtlasFirstJet A G i x) (probeAtlasFirstJet A F i x) hjetG hjetF hgram
  rw [hnorm] at h
  convert h using 1; ring

/-- A genuine reference constant works on every original support and for
every same-metric smooth perturbation. Empty supports and zero dimensional
source/normal spaces require no extra hypotheses. -/
theorem exists_uniform_sameMetric_normalProjection_budget
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) →
      ∀ b : ℝ, 0 ≤ b → probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal b →
      ∀ i x, x ∈ A.support i →
        ‖(normalSpace (I := IM) G x).starProjection -
          (normalSpace (I := IM) F x).starProjection‖ ≤ C * b := by
  have hc (i : Fin A.count) : ContinuousOn
      (fun x ↦ ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖)
      (A.support i) :=
    ((continuousOn_probeAtlasGramInverse A hA F hF himm i).norm.mul
      (continuousOn_probeAtlasFirstJet A hA F hF i).norm).mono (hA.support_subset i)
  choose B hB using fun i ↦ (hcompact i).exists_bound_of_continuousOn (hc i)
  obtain ⟨C, hC⟩ := Finite.exists_le B
  let K := |C| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let D := probeAtlasDerivativeConstant n N 1
  have hD : 0 ≤ D := probeAtlasDerivativeConstant_nonneg n N 1
  refine ⟨2 * K * D + 1, by positivity, ?_⟩
  intro G hG hmetric b hb hbudget i x hx
  have hbase : ‖((probeAtlasFirstJet A F i x).adjoint.comp
      (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖ ≤ K := by
    calc
      _ ≤ ‖‖((probeAtlasFirstJet A F i x).adjoint.comp
          (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖‖ :=
        le_abs_self _
      _ ≤ B i := hB i x hx
      _ ≤ K := (hC i).trans ((le_abs_self C).trans (by dsimp [K]; linarith))
  have hfactor : 2 * ‖((probeAtlasFirstJet A F i x).adjoint.comp
      (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖ ≤ 2 * K := by
    nlinarith
  have hjet := (probeAtlas_original_two_jet_difference A hA F G hF hG hb hbudget i x hx).1
  have hproj := trueNormalProjection_gap_of_sameMetric_firstJet A hA F G hF hG i x
    (hA.support_subset i hx) (himm x) (hmetric x)
  calc
    _ ≤ (2 * ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖) *
          ‖probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x‖ := hproj
    _ ≤ (2 * K) * (D * b) := mul_le_mul hfactor hjet (norm_nonneg _) (by positivity)
    _ ≤ (2 * K * D + 1) * b := by nlinarith

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.trueNormalProjection_gap_of_sameMetric_firstJet
#print axioms GlobalEmbedding.NormalPolar.exists_uniform_sameMetric_normalProjection_budget
