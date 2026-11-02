import Upgrade.CompactNormalizedReference
import Upgrade.SupportedIdentifiedHessian

/-!
# Original C² and the selected identification control the actual incidence form

This is the zeroth-order geometric bridge to the fixed Schur or supported
normal chart. The old Hessian, new Hessian, true form and source normalization
are the literal objects already used by the actual incidence. Map closeness
is measured in the original atlas norm. Closeness of the chosen normal
identification is kept as its own explicit upstream input.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms

section Operators
variable {S W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem fixed_identified_hessian_error
    (PN : W →L[ℝ] Z) (Q P : W →L[ℝ] W)
    (H H₀ : S →L[ℝ] W) (K : S →L[ℝ] S)
    (hPN : ‖PN‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖PN.comp ((Q.comp H).comp K) - PN.comp ((P.comp H₀).comp K)‖ ≤
      (‖H - H₀‖ + ‖Q - P‖ * ‖H₀‖) * ‖K‖ := by
  have heq : Q.comp H - P.comp H₀ =
      Q.comp (H - H₀) + (Q - P).comp H₀ := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  have hinner : ‖Q.comp H - P.comp H₀‖ ≤ ‖H - H₀‖ + ‖Q - P‖ * ‖H₀‖ := by
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
    · exact ContinuousLinearMap.opNorm_comp_le _ _
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖PN‖ * ‖(Q.comp H - P.comp H₀).comp K‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(Q.comp H - P.comp H₀).comp K‖ :=
      mul_le_mul_of_nonneg_right hPN (norm_nonneg _)
    _ ≤ (‖H - H₀‖ + ‖Q - P‖ * ‖H₀‖) * ‖K‖ := by
      rw [one_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hinner (norm_nonneg _))

end Operators

attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual incidence form is close to the same actual old normalized
form. The bound contains the exact original C² comparison constant, the
fixed source normalization norm and the chosen identification's actual gap. -/
theorem actualSupportedProbeCoordinate_sub_reference_bound
    {P : Type*} (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (u : P) (z : M) (hz : z ∈ A.support i)
    {b : ℝ} (hb : 0 ≤ b) (hclose : probeAtlasCj A 2 (G u - F₀) ≤ ENNReal.ofReal b) :
    ‖actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u, A.chart i z) -
      normalizedReferenceForm A hA F₀ i x hx z‖ ≤
      ((actualHessianLiftConstant E V * probeAtlasDerivativeConstant n N 2) * b +
        ‖normalIdentificationOperator (n := n) F₀ (G u) (Q u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ * ‖probeAtlasSecondJet A F₀ i z‖) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖ := by
  have hzs := hA.support_subset i hz
  have hzt := (A.chart i).map_source hzs
  have htrue := actualSupportedProbeCoordinate_eq_identified_hessian F₀ G hG Q
    A hA i x hx (u, A.chart i z) hzt
  simp only [(A.chart i).left_inv hzs] at htrue
  have hnormal := normalSpace_eq_probeAtlasFirstJet_range A hA F₀ hF₀ i z hzs
  have href : normalizedReferenceForm A hA F₀ i x hx z =
      (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
        (((normalSpace (I := IM) F₀ z).starProjection.comp
          (probeAtlasSecondJet A F₀ i z)).comp (probeAtlasNormalizationSquare A hA i x hx)) := by
    unfold normalizedReferenceForm fixedAtlasNormalForm probeAtlasProjectedSecondForm
    rw [hnormal, ContinuousLinearMap.comp_assoc]
  have hPN : ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [one_mul] using (normalSpace (I := IM) F₀ x).norm_orthogonalProjectionOnto_apply_le v
  have hjet := (probeAtlas_original_two_jet_difference A hA F₀ (G u) hF₀ (hG u)
    hb hclose i z hz).2
  rw [htrue, href]
  have h := fixed_identified_hessian_error
    (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
    (normalIdentificationOperator (n := n) F₀ (G u) (Q u) z)
    (normalSpace (I := IM) F₀ z).starProjection
    (probeAtlasSecondJet A (G u) i z) (probeAtlasSecondJet A F₀ i z)
    (probeAtlasNormalizationSquare A hA i x hx) hPN
    (normalIdentificationOperator_norm_le_one F₀ (G u) (Q u) z)
  exact h.trans (mul_le_mul_of_nonneg_right
    (add_le_add hjet le_rfl) (norm_nonneg _))

/-- Specialization to the original full probe family. The sole additional
quantity in this explicit bound is the actual chosen identification gap. -/
theorem ExactProbeFamily.actual_form_sub_reference_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (z : M) (hz : z ∈ A.support i) :
    ‖actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, A.chart i z) -
      normalizedReferenceForm A hA F₀ i x hx z‖ ≤
      ((actualHessianLiftConstant E V * probeAtlasDerivativeConstant n N 2) *
          (probe.constant * t ^ ((44 : ℝ) / 5)) +
        ‖normalIdentificationOperator (n := n) F₀ (probe.map t u)
            (probe.normalIdentification t u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ * ‖probeAtlasSecondJet A F₀ i z‖) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖ :=
  actualSupportedProbeCoordinate_sub_reference_bound F₀ hF₀ (probe.map t)
    (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hx u z hz
    (mul_nonneg probe.constant_nonneg (Real.rpow_nonneg ht.le _)) (probe.closeness t ht htt u hu)

#print axioms actualSupportedProbeCoordinate_sub_reference_bound
#print axioms ExactProbeFamily.actual_form_sub_reference_bound

end GlobalEmbedding.Upgrade
