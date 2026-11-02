import NormalPolar.ResponseProbeGeometry
import Round2.MetricLeftInverseCompact

/-!
# Uniform same-Q parameter response on the original compact supports

The constants are selected from the fixed reference immersion, original atlas
and fixed polar reserve before the actual family or its parameter points.
The general open-domain result consumes a genuine first-jet response budget.
The original-interface result derives this input from the original C¹ norm of
the actual parameter derivative, using the existing mixed-derivative bridge.
No normal-identification response is supplied as an assumption.
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

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- A positive reference coefficient, uniform on every original support.
The coefficient uses actual reference Gram inverses and first jets. -/
theorem exists_uniform_reference_normal_response_factor
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    ∃ K : ℝ, 0 < K ∧ ∀ i z, z ∈ A.support i →
      2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
        (probeAtlasFirstJet A F₀ i z)).inverse‖ *
          ‖probeAtlasFirstJet A F₀ i z‖ ≤ K := by
  have hc (i : Fin A.count) : ContinuousOn
      (fun z ↦ ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
        (probeAtlasFirstJet A F₀ i z)).inverse‖ * ‖probeAtlasFirstJet A F₀ i z‖)
      (A.support i) :=
    ((continuousOn_probeAtlasGramInverse A hA F₀ hF₀ hi₀ i).norm.mul
      (continuousOn_probeAtlasFirstJet A hA F₀ hF₀ i).norm).mono (hA.support_subset i)
  choose B hB using fun i ↦ (hcompact i).exists_bound_of_continuousOn (hc i)
  obtain ⟨K, hK⟩ := Finite.exists_le B
  refine ⟨2 * (|K| + 1), by positivity, ?_⟩
  intro i z hz
  have hbase : ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
      (probeAtlasFirstJet A F₀ i z)).inverse‖ * ‖probeAtlasFirstJet A F₀ i z‖ ≤
        |K| + 1 := by
    calc
      _ ≤ ‖‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
          (probeAtlasFirstJet A F₀ i z)).inverse‖ * ‖probeAtlasFirstJet A F₀ i z‖‖ :=
        le_abs_self _
      _ ≤ B i := hB i z hz
      _ ≤ |K| + 1 := (hK i).trans ((le_abs_self K).trans (by linarith))
  nlinarith

section OpenParameterDomain
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A reference constant works for every later actual family on its unchanged
open parameter domain. The first-jet differentiability and response budget
refer to the actual mapping family, never to Q. -/
theorem exists_uniform_actualImmersionNormalIdentification_response_from_firstJet
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (q : ℝ) (hq : q < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : P → M → V) (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
        (hi : ∀ u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x))
        (U : Set P), IsOpen U →
        (∀ v ∈ U, ∀ x, inducedMetric (I := IM) (F v) x = inducedMetric (I := IM) F₀ x) →
        (∀ v ∈ U, ∀ x, ‖(normalSpace (I := IM) F₀ x).starProjection -
          (normalSpace (I := IM) (F v) x).starProjection‖ ≤ q) →
        ∀ u d, u ∈ U → ∀ i z, z ∈ A.support i →
        DifferentiableAt ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u →
        ∀ b : ℝ, 0 ≤ b →
        ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u d‖ ≤ b →
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v)
          (actualImmersionNormalIdentification F₀ (F v) hi₀ (hi v)) z) u d‖ ≤ C * b := by
  obtain ⟨K, hK, hfactor⟩ :=
    exists_uniform_reference_normal_response_factor A hA hcompact F₀ hF₀ hi₀
  have hpolar := polarResponseConstantOn_nonneg («V» := V) q hq
  refine ⟨polarResponseConstantOn V q hq * K + 1, by positivity, ?_⟩
  intro F hF hi U hU hmetric hgap u d hu i z hz hfirst b hb hbudget
  have hpoint := norm_fderiv_actualImmersionNormalIdentification_from_firstJet_le
    F₀ F hF₀ hF hi₀ hi A hA i z (hA.support_subset i hz) hU u d hu q hq hfirst
    (fun v hv ↦ hmetric v hv z) (fun v hv ↦ hgap v hv z)
  rw [probeAtlasFirstJet_norm_eq_of_inducedMetric_eq A hA F₀ (F u) hF₀ (hF u)
    i z (hA.support_subset i hz) (hmetric u hu z)] at hpoint
  calc
    _ ≤ polarResponseConstantOn V q hq *
        (2 * ‖((probeAtlasFirstJet A F₀ i z).adjoint.comp
          (probeAtlasFirstJet A F₀ i z)).inverse‖ * ‖probeAtlasFirstJet A F₀ i z‖ *
            ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (F v) i z) u d‖) := hpoint
    _ ≤ polarResponseConstantOn V q hq * (K * b) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hfactor i z hz) hbudget (norm_nonneg _) hK.le) hpolar
    _ ≤ (polarResponseConstantOn V q hq * K + 1) * b := by nlinarith

end OpenParameterDomain

/-- The original C¹ parameter-response budget gives one uniform constant for
all subsequently constructed actual probe geometries. The constant precedes
the wave count, family, radius, threshold, scale, parameter, direction and
source point. The geometry and its original parameter ball are unchanged. -/
theorem exists_uniform_actualProbeGeometry_normal_response_originalC1
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (q : ℝ) (hq : q < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℕ} (F : ℝ → ProbeParameters r → M → V)
      (radius threshold : ℝ) (hradius : 0 < radius) (hthreshold : 0 < threshold)
      (hF : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
      (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
      (hjoint : ∀ t, 0 < t → t < threshold →
        ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
          (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
      (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
        inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
      (hgap : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
        ‖(normalSpace (I := IM) F₀ x).starProjection -
          (normalSpace (I := IM) (F t u) x).starProjection‖ ≤ q),
      let geometry := probeGeometryOfActualImmersions F₀ hF₀ hi₀ F radius threshold
        hradius hthreshold hF hi hjoint hmetric
        (fun t ht htt u hu x ↦ (hgap t ht htt u hu x).trans_lt hq)
      ∀ t, 0 < t → t < threshold → ∀ u d, ‖u‖ < radius →
        ∀ i z, z ∈ A.support i → ∀ b : ℝ, 0 ≤ b →
        probeAtlasCj A 1 (fun y ↦ fderiv ℝ (fun v ↦ F t v y) u d) ≤ ENNReal.ofReal b →
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (geometry.map t v)
          (geometry.normalIdentification t v) z) u d‖ ≤ C * b := by
  obtain ⟨K, hK, hfactor⟩ :=
    exists_uniform_reference_normal_response_factor A hA hcompact F₀ hF₀ hi₀
  have hpolar := polarResponseConstantOn_nonneg («V» := V) q hq
  have hD := probeAtlasDerivativeConstant_nonneg n N 1
  refine ⟨polarResponseConstantOn V q hq * K * probeAtlasDerivativeConstant n N 1 + 1,
    by positivity, ?_⟩
  intro r F radius threshold hradius hthreshold hF hi hjoint hmetric hgap
  dsimp only
  intro t ht htt u d hu i z hz b hb hbudget
  have hpoint := actualProbeGeometry_normal_response_from_originalC1 F₀ hF₀ hi₀ F
    radius threshold hradius hthreshold hF hi hjoint hmetric q hq hgap
    A hA i t ht htt u d hu z hz hb hbudget
  apply hpoint.trans
  calc
    _ ≤ polarResponseConstantOn V q hq * (K * (probeAtlasDerivativeConstant n N 1 * b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hfactor i z hz) (mul_nonneg hD hb)) hpolar
    _ ≤ (polarResponseConstantOn V q hq * K * probeAtlasDerivativeConstant n N 1 + 1) * b := by
      nlinarith

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_uniform_reference_normal_response_factor
#print axioms GlobalEmbedding.NormalPolar.exists_uniform_actualImmersionNormalIdentification_response_from_firstJet
#print axioms GlobalEmbedding.NormalPolar.exists_uniform_actualProbeGeometry_normal_response_originalC1
