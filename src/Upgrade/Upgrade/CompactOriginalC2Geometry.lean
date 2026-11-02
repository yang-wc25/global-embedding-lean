import Upgrade.CompactFixedAtlasPhase

/-!
# Original C² control of the actual normal geometry

The error terms are literal differences of actual normal projectors and actual
projected second forms in the fixed original atlas. They are derived from the
original norm, not assumed as independent coefficients or from an arbitrary
orthogonal identification. Both the Gram reserve and Hessian bound are taken
from the actual compact reference geometry.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Every prescribed positive geometric error admits one original C² budget,
valid for every later smooth map and every original compact support point.
The first conclusion controls the actual global normal projector; the second
controls the actual true form in the proved fixed source coordinates. -/
theorem exists_originalC2_normal_and_form_budget
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) {d : ℝ} (hd : 0 < d) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      (∀ x, ‖(normalSpace (I := IM) G x).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ < d) ∧
      (∀ i x, x ∈ A.support i →
        ‖probeAtlasProjectedSecondForm A G i x -
          probeAtlasProjectedSecondForm A F i x‖ < d) := by
  obtain ⟨lam, B, m, hlam, hB, _, hbase⟩ :=
    exists_fixedAtlas_actual_reference_reserves A hA hcompact hdim F hF himm hphase
  let c := 3 / Real.sqrt lam
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let L := 1 + c + c * B
  have hL : 0 < L := by dsimp only [L]; positivity
  let δ := min (Real.sqrt lam / 2) (d / (2 * L))
  have hδ : 0 < δ := lt_min (div_pos (Real.sqrt_pos.mpr hlam) (by norm_num))
    (div_pos hd (by positivity))
  have hLδ : L * δ ≤ d / 2 := by
    have h := mul_le_mul_of_nonneg_left
      (min_le_right (Real.sqrt lam / 2) (d / (2 * L))) hL.le
    have he : L * (d / (2 * L)) = d / 2 := by field_simp
    exact h.trans_eq he
  let C1 := probeAtlasDerivativeConstant n N 1
  let C2 := actualHessianLiftConstant E V * probeAtlasDerivativeConstant n N 2
  have hC1 : 0 ≤ C1 := probeAtlasDerivativeConstant_nonneg _ _ _
  have hC2 : 0 ≤ C2 := mul_nonneg
    (show 0 ≤ actualHessianLiftConstant E V from actualHessianLiftConstant_nonneg)
    (probeAtlasDerivativeConstant_nonneg _ _ _)
  let K := 1 + C1 + C2
  have hK : 0 < K := by dsimp only [K]; positivity
  let e := δ / K
  have he : 0 < e := div_pos hδ hK
  have hKe : K * e = δ := by dsimp only [e]; field_simp
  have hC1e : C1 * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith : C1 ≤ K) he.le).trans_eq hKe
  have hC2e : C2 * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith : C2 ≤ K) he.le).trans_eq hKe
  refine ⟨e, he, ?_⟩
  intro G hG hbudget
  have hpoint (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖(normalSpace (I := IM) G x).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ < d ∧
      ‖probeAtlasProjectedSecondForm A G i x -
        probeAtlasProjectedSecondForm A F i x‖ < d := by
    have hj := probeAtlas_original_two_jet_difference A hA F G hF hG he.le hbudget i x hx
    have hfirst : ‖probeAtlasFirstJet A F i x - probeAtlasFirstJet A G i x‖ ≤ δ := by
      rw [norm_sub_rev]
      exact hj.1.trans hC1e
    have hsecond : ‖probeAtlasSecondJet A G i x - probeAtlasSecondJet A F i x‖ ≤ δ :=
      hj.2.trans hC2e
    have hsmall := hfirst.trans (min_le_left _ _)
    have hprojection := pointwise_projected_jet_estimate
      (probeAtlasFirstJet A F i x) (probeAtlasFirstJet A G i x)
      (ContinuousLinearMap.id ℝ V) (ContinuousLinearMap.id ℝ V)
      lam 1 hlam (hbase i x hx).1 hsmall ContinuousLinearMap.norm_id_le
    have hprojF : (normalSpace (I := IM) F x).starProjection =
        (probeAtlasFirstJet A F i x).rangeᗮ.starProjection := by
      congr 1
      exact normalSpace_eq_probeAtlasFirstJet_range A hA F hF i x (hA.support_subset i hx)
    have hprojG : (normalSpace (I := IM) G x).starProjection =
        (probeAtlasFirstJet A G i x).rangeᗮ.starProjection := by
      congr 1
      exact normalSpace_eq_probeAtlasFirstJet_range A hA G hG i x (hA.support_subset i hx)
    have hprojector : ‖(normalSpace (I := IM) G x).starProjection -
        (normalSpace (I := IM) F x).starProjection‖ ≤ c * δ := by
      rw [hprojG, hprojF]
      have hp : ‖(probeAtlasFirstJet A G i x).rangeᗮ.starProjection -
          (probeAtlasFirstJet A F i x).rangeᗮ.starProjection‖ ≤
            c * ‖probeAtlasFirstJet A F i x - probeAtlasFirstJet A G i x‖ := by
        simpa only [ContinuousLinearMap.comp_id, sub_self, norm_zero, zero_add, mul_one]
          using hprojection.2
      exact hp.trans (mul_le_mul_of_nonneg_left hfirst hc)
    have hform := pointwise_projected_jet_estimate
      (probeAtlasFirstJet A F i x) (probeAtlasFirstJet A G i x)
      (probeAtlasSecondJet A F i x) (probeAtlasSecondJet A G i x)
      lam B hlam (hbase i x hx).1 hsmall (hbase i x hx).2.1
    have hformbound : ‖probeAtlasProjectedSecondForm A G i x -
        probeAtlasProjectedSecondForm A F i x‖ ≤ (1 + c * B) * δ := by
      have h := hform.2.trans (add_le_add hsecond
        (mul_le_mul_of_nonneg_left hfirst (mul_nonneg hc hB)))
      have hid : δ + c * B * δ = (1 + c * B) * δ := by ring
      exact h.trans_eq hid
    have hprojhalf : c * δ ≤ d / 2 :=
      (mul_le_mul_of_nonneg_right (by dsimp only [L]; nlinarith : c ≤ L) hδ.le).trans hLδ
    have hformhalf : (1 + c * B) * δ ≤ d / 2 :=
      (mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith : 1 + c * B ≤ L) hδ.le).trans hLδ
    exact ⟨hprojector.trans hprojhalf |>.trans_lt (half_lt_self hd),
      hformbound.trans hformhalf |>.trans_lt (half_lt_self hd)⟩
  constructor
  · intro x
    obtain ⟨i, hx⟩ := hcover x
    exact (hpoint i x hx).1
  · intro i x hx
    exact (hpoint i x hx).2

end GlobalEmbedding.Upgrade
