import Upgrade.CompactFixedAtlasPhaseGeometry
import Upgrade.ProtectionMargins

/-!
# Original C² phase protection on finitely many actual atlas supports

All reference constants below are extracted from the actual current immersion
on the finite disjoint union of the original compact enlarged supports. The
original C² norm supplies both literal coordinate jet errors. The conclusion
is the original `PhaseRegular` predicate, together with a fixed-chart positive
margin and immersion bound; none is supplied as a perturbed-map hypothesis.
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

/-- The actual current immersion has common positive Gram and phase reserves
and a finite Hessian bound on all original compact supports. No nonemptiness
or connectedness assumption enters the finite disjoint union argument. -/
theorem exists_fixedAtlas_actual_reference_reserves
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i)) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) :
    ∃ lam B m : ℝ, 0 < lam ∧ 0 ≤ B ∧ 0 < m ∧
      ∀ i x, x ∈ A.support i →
        (∀ v, lam * ‖v‖ ^ 2 ≤ ‖probeAtlasFirstJet A F i x v‖ ^ 2) ∧
        ‖probeAtlasSecondJet A F i x‖ ≤ B ∧
        m ≤ bestPhaseSupremum (probeAtlasProjectedSecondForm A F i x) := by
  letI : ∀ i, CompactSpace (A.support i) := fun i ↦
    isCompact_iff_compactSpace.mp (hcompact i)
  let J := Σ i : Fin A.count, A.support i
  let first : J → E →L[ℝ] V := fun z ↦ probeAtlasFirstJet A F z.1 z.2
  let second : J → SymmetricSquare E →L[ℝ] V := fun z ↦ probeAtlasSecondJet A F z.1 z.2
  let projected : J → SymmetricSquare E →L[ℝ] V := fun z ↦
    probeAtlasProjectedSecondForm A F z.1 z.2
  have hfirst : Continuous first := continuous_sigma_iff.mpr fun i ↦
    ((continuousOn_probeAtlasFirstJet A hA F hF i).mono (hA.support_subset i)).domRestrict
  have hsecond : Continuous second := continuous_sigma_iff.mpr fun i ↦
    ((continuousOn_probeAtlasSecondJet A hA F hF i).mono (hA.support_subset i)).domRestrict
  have hprojected : Continuous projected := continuous_sigma_iff.mpr fun i ↦
    ((continuousOn_probeAtlasProjectedSecondForm A hA F hF himm i).mono
      (hA.support_subset i)).domRestrict
  obtain ⟨lam, hlam, hgram⟩ := free_compact_frame_lower_bound first hfirst
    (fun z ↦ probeAtlasFirstJet_injective A hA F hF z.1 z.2
      (hA.support_subset z.1 z.2.property) (himm z.2))
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set J))
    |>.exists_bound_of_continuousOn hsecond.continuousOn
  have hd : 2 ≤ finrank ℝ E := by simpa using hdim
  obtain ⟨m, hm, hmarg⟩ := compact_positive_lower_bound
    (isCompact_univ : IsCompact (univ : Set J))
    (((bestPhaseSupremum_lipschitz (F := V) hd).continuous.comp hprojected).continuousOn)
    (fun z _ ↦ bestPhaseSupremum_pos_of_linearPhase hd (projected z)
      ((probeAtlasProjectedSecondForm_phase_iff A hA F hF z.1 z.2
        (hA.support_subset z.1 z.2.property)).mpr
          (trueSecondForm_linearPhaseRegular F hF hphase z.2)))
  refine ⟨lam, max 0 B, m, hlam, le_max_left _ _, hm, ?_⟩
  intro i x hx
  exact ⟨hgram ⟨i, x, hx⟩, (hB ⟨i, x, hx⟩ (mem_univ _)).trans
    (le_max_right _ _), (hmarg ⟨i, x, hx⟩ (mem_univ _)).le⟩

/-- A single original C² tolerance protects the original phase predicate on
the complete source. It also protects quantitative first-jet and fixed-chart
phase margins. All constants are selected from the actual reference map and
original compact atlas; later maps need only be smooth and meet that norm bound. -/
theorem exists_originalC2_phase_protection
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) :
    ∃ e lam m : ℝ, 0 < e ∧ 0 < lam ∧ 0 < m ∧
      ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
        probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
        PhaseRegular G hG ∧
          ∀ i x, x ∈ A.support i →
            (∀ v, lam * ‖v‖ ^ 2 ≤ ‖probeAtlasFirstJet A G i x v‖ ^ 2) ∧
            m ≤ bestPhaseSupremum (probeAtlasProjectedSecondForm A G i x) := by
  obtain ⟨lam, B, m, hlam, hB, hm, hbase⟩ :=
    exists_fixedAtlas_actual_reference_reserves A hA hcompact hdim F hF himm hphase
  let c := (3 / Real.sqrt lam) * B
  have hc : 0 ≤ c := mul_nonneg (by positivity) hB
  let δ := min (Real.sqrt lam / 2) (m / (2 * (1 + c)))
  have hδ : 0 < δ := lt_min (div_pos (Real.sqrt_pos.mpr hlam) (by norm_num))
    (div_pos hm (by positivity))
  have hδm : (1 + c) * δ ≤ m / 2 := by
    have h := mul_le_mul_of_nonneg_left
      (min_le_right (Real.sqrt lam / 2) (m / (2 * (1 + c)))) (by positivity : 0 ≤ 1 + c)
    have he : (1 + c) * (m / (2 * (1 + c))) = m / 2 := by field_simp
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
  refine ⟨e, lam / 4, m / 2, he, by positivity, by positivity, ?_⟩
  intro G hG hbudget
  have hpoint (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖probeAtlasFirstJet A G i x v‖ ^ 2) ∧
        m / 2 ≤ bestPhaseSupremum (probeAtlasProjectedSecondForm A G i x) := by
    have hj := probeAtlas_original_two_jet_difference A hA F G hF hG he.le hbudget i x hx
    have hfirst : ‖probeAtlasFirstJet A F i x - probeAtlasFirstJet A G i x‖ ≤ δ := by
      rw [norm_sub_rev]
      exact hj.1.trans hC1e
    have hsecond : ‖probeAtlasSecondJet A G i x - probeAtlasSecondJet A F i x‖ ≤ δ :=
      hj.2.trans hC2e
    have h := pointwise_projected_jet_estimate
      (probeAtlasFirstJet A F i x) (probeAtlasFirstJet A G i x)
      (probeAtlasSecondJet A F i x) (probeAtlasSecondJet A G i x)
      lam B hlam (hbase i x hx).1 (hfirst.trans (min_le_left _ _)) (hbase i x hx).2.1
    have hnorm : ‖probeAtlasProjectedSecondForm A G i x -
        probeAtlasProjectedSecondForm A F i x‖ ≤ m / 2 := by
      have hb := add_le_add hsecond (mul_le_mul_of_nonneg_left hfirst hc)
      have hid : δ + c * δ = (1 + c) * δ := by ring
      exact h.2.trans (hb.trans (hid.le.trans hδm))
    have hdiff := bestPhaseSupremum_sub_le (by simpa using hdim)
      (probeAtlasProjectedSecondForm A F i x) (probeAtlasProjectedSecondForm A G i x)
    rw [norm_sub_rev] at hdiff
    exact ⟨h.1, by have hp := (hbase i x hx).2.2; linarith⟩
  refine ⟨phaseRegular_of_probeAtlas_positive_margin A hA hcover hdim G hG ?_, hpoint⟩
  intro i x hx
  exact (half_pos hm).trans_le (hpoint i x hx).2

end GlobalEmbedding.Upgrade
