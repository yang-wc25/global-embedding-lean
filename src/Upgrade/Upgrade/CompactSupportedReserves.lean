import Upgrade.ProtectionSupported
import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates

/-!
# Finite actual source/normal reserves for the nonsupported region

Both compared forms below are literal true second forms.  They use the same
old source chart and the same fixed old normal projection.  The candidate map
is not assumed phase regular, full rank, or already free of supported kernels.
Small actual projection and coefficient errors imply full rank and absence of
supported kernels on the whole compact region.  An arbitrary orthogonal
identification is not used.
-/

noncomputable section
open Set Bundle Manifold Topology GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- The actual candidate form in an old fixed normal target and an old fixed
source chart.  Source frame variation is part of this literal definition. -/
def actualFixedNormalForm
    (F G : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G) (center z : M) :
    SymmetricSquare E →L[ℝ] normalSpace (I := I) F center :=
  (normalSpace (I := I) F center).orthogonalProjectionOnto.comp
    (LinearMap.toContinuousLinearMap
      ((normalSpace (I := I) G z).subtype.comp
        ((trueSecondForm G hG z).comp
          (symmetricSquareLinearMap
            ((trivializationAt E (TangentSpace I) center).symmL ℝ z).toLinearMap))))

/-- Actual normal/source coordinates preserve supportedness and reflect
surjectivity whenever their normal projection gap is below one. -/
theorem actualFixedNormalForm_geometry
    (F G : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G) (center z : M)
    (hz : z ∈ (chartAt H center).source)
    (hgap : ‖(normalSpace (I := I) G z).starProjection -
      (normalSpace (I := I) F center).starProjection‖ < 1) :
    (HasSupportedKernel (actualFixedNormalForm F G hG center z).toLinearMap ↔
      HasSupportedKernel (trueSecondForm G hG z)) ∧
    (Function.Surjective (actualFixedNormalForm F G hG center z) →
      Function.Surjective (trueSecondForm G hG z)) := by
  let j := (normalSpace (I := I) F center).orthogonalProjectionOnto.comp
    (normalSpace (I := I) G z).subtypeL
  have hj : Function.Injective j := normal_coordinate_injective _ _ hgap
  have hz0 : z ∈ (trivializationAt E (TangentSpace I) center).baseSet := hz
  let e : E ≃L[ℝ] E :=
    ((trivializationAt E (TangentSpace I) center).continuousLinearEquivAt ℝ z hz0).symm
  have he : e.toLinearMap =
      ((trivializationAt E (TangentSpace I) center).symmL ℝ z).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap
      ((trivializationAt E (TangentSpace I) center).symm_continuousLinearEquivAt_eq' hz0)
  have hdict : (actualFixedNormalForm F G hG center z).toLinearMap =
      j.toLinearMap.comp
        ((show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) G z from trueSecondForm G hG z).comp
          (symmetricSquareLinearMap e.toLinearMap)) := by
    apply LinearMap.ext
    intro q
    rw [he]
    rfl
  constructor
  · rw [hdict, hasSupportedKernel_postcomp_iff _ _ hj]
    exact hasSupportedKernel_source_coordinates_iff
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) G z from trueSecondForm G hG z) e
  · intro honto v
    obtain ⟨q, hq⟩ := honto (j v)
    refine ⟨symmetricSquareLinearMap e.toLinearMap q, hj ?_⟩
    have hqe := congrArg (fun T : SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F center ↦ T q)
      hdict
    exact hqe.symm.trans hq

theorem isOpen_operator_nonsupported
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    IsOpen {B : SymmetricSquare E →L[ℝ] W |
      Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap ∧
        ¬ HasSupportedKernel B.toLinearMap} := by
  have ho := (isOpen_surjective_linearSecondFormPhaseRegular
    (V := E) (W := W)).isOpenMap_subtype_val _
      (isClosed_supportedKernel_surjective_phaseRegular (V := E) (W := W)).isOpen_compl
  convert ho using 1
  ext B
  simp only [mem_ofPred_eq, mem_image, mem_compl_iff]
  constructor
  · rintro ⟨honto, hphase, hnot⟩
    exact ⟨⟨B, honto, hphase⟩, hnot, rfl⟩
  · rintro ⟨C, hnot, rfl⟩
    exact ⟨C.property.1, C.property.2, hnot⟩

/-- Finite actual geometric reserves for any current compact full-rank
nonsupported set.  Each original normal projection varies by less than one
half on the selected compact closure. One common error radius then controls
all later maps through literal first- and second-form quantities.

The two displayed error estimates are still caller obligations; in the
upgrade they must follow from the original probes' C² control on this finite
fixed atlas. They do not assert the desired incidence or rank conclusion. -/
theorem exists_finite_actual_nonsupported_reserves
    [T2Space M] [LocallyCompactSpace M] [RegularSpace M]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hgood : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x)) :
    ∃ centers : Finset C, ∃ U : C → Set M, ∃ e > 0,
      (∀ c, IsOpen (U c) ∧ c.1 ∈ U c ∧ IsCompact (closure (U c)) ∧
        closure (U c) ⊆ (chartAt H c.1).source ∧
        ∀ z ∈ closure (U c),
          ‖(normalSpace (I := I) F z).starProjection -
            (normalSpace (I := I) F c.1).starProjection‖ < (1 / 2 : ℝ)) ∧
      (∀ x ∈ C, ∃ c ∈ centers, x ∈ U c) ∧
      ∀ (G : M → EuclideanSpace ℝ (Fin N))
        (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G),
        (∀ c ∈ centers, ∀ z ∈ closure (U c),
          ‖(normalSpace (I := I) G z).starProjection -
            (normalSpace (I := I) F z).starProjection‖ < e ∧
          ‖actualFixedNormalForm F G hG c.1 z -
            actualFixedNormalForm F F hF c.1 z‖ < e) →
        ∀ x ∈ C, Function.Surjective (trueSecondForm G hG x) ∧
          ¬ HasSupportedKernel (trueSecondForm G hG x) := by
  classical
  have hlocal (c : C) : ∃ U : Set M, ∃ e > 0,
      IsOpen U ∧ c.1 ∈ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (chartAt H c.1).source ∧
      (∀ z ∈ closure U,
        ‖(normalSpace (I := I) F z).starProjection -
          (normalSpace (I := I) F c.1).starProjection‖ < (1 / 2 : ℝ)) ∧
      ∀ (G : M → EuclideanSpace ℝ (Fin N))
        (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G) z, z ∈ closure U →
        ‖(normalSpace (I := I) G z).starProjection -
          (normalSpace (I := I) F z).starProjection‖ < (1 / 4 : ℝ) →
        ‖actualFixedNormalForm F G hG c.1 z -
          actualFixedNormalForm F F hF c.1 z‖ < e →
        Function.Surjective (trueSecondForm G hG z) ∧
          ¬ HasSupportedKernel (trueSecondForm G hG z) := by
    obtain ⟨V, D, hV, hcV, hVchart, hDsmooth, hDc, hDvalue, hDgeometry⟩ :=
      exists_actual_supported_coordinate_field F hF himm c.1
    have hD (z : M) : actualFixedNormalForm F F hF c.1 z = D z := by
      apply ContinuousLinearMap.ext
      intro q
      exact (hDvalue z q).symm
    have hDgood : D c.1 ∈ {B : SymmetricSquare E →L[ℝ] normalSpace (I := I) F c.1 |
        Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap ∧
          ¬ HasSupportedKernel B.toLinearMap} := by
      rw [hDc]
      exact ⟨(hgood c.1 c.2).1, trueSecondForm_linearPhaseRegular F hF hphase c.1,
        (hgood c.1 c.2).2⟩
    obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp isOpen_operator_nonsupported _ hDgood
    have hDa : ContinuousAt D c.1 := (hDsmooth.contMDiffAt (hV.mem_nhds hcV)).continuousAt
    have hnear : {z | dist (D z) (D c.1) < a / 4} ∈ 𝓝 c.1 := by
      change D ⁻¹' Metric.ball (D c.1) (a / 4) ∈ 𝓝 c.1
      exact hDa.preimage_mem_nhds
        (Metric.ball_mem_nhds (D c.1) (show 0 < a / 4 by positivity))
    obtain ⟨Q, hQsub, hQ, hcQ⟩ := mem_nhds_iff.mp hnear
    obtain ⟨Vn, hVn, hcVn, _, hnormal⟩ :=
      exists_fixed_normal_coordinate_neighborhood F hF himm c.1
    obtain ⟨U, hU, hcU, hUsub, hUcompact⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton
        ((hV.inter hVn).inter hQ)
        (singleton_subset_iff.mpr ⟨⟨hcV, hcVn⟩, hcQ⟩)
    have hUchart : closure U ⊆ (chartAt H c.1).source :=
      fun z hz ↦ hVchart (hUsub hz).1.1
    have hUprojection : ∀ z ∈ closure U,
        ‖(normalSpace (I := I) F z).starProjection -
          (normalSpace (I := I) F c.1).starProjection‖ < (1 / 2 : ℝ) :=
      fun z hz ↦ (hnormal z (hUsub hz).1.2).1
    refine ⟨U, a / 4, by positivity, hU, hcU (mem_singleton c.1), hUcompact,
      hUchart, hUprojection, ?_⟩
    intro G hG z hz hproj hform
    have hnewgap : ‖(normalSpace (I := I) G z).starProjection -
        (normalSpace (I := I) F c.1).starProjection‖ < 1 := by
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (normalSpace (I := I) G z).starProjection
        (normalSpace (I := I) F z).starProjection
        (normalSpace (I := I) F c.1).starProjection
      have hold := hUprojection z hz
      linarith
    have hbase : dist (D z) (D c.1) < a / 4 := hQsub (hUsub hz).2
    have hnewball : actualFixedNormalForm F G hG c.1 z ∈ Metric.ball (D c.1) a := by
      change dist (actualFixedNormalForm F G hG c.1 z) (D c.1) < a
      have htri := dist_triangle (actualFixedNormalForm F G hG c.1 z) (D z) (D c.1)
      have hstep : dist (actualFixedNormalForm F G hG c.1 z) (D z) < a / 4 := by
        rw [← hD z]
        calc
          dist (actualFixedNormalForm F G hG c.1 z)
              (actualFixedNormalForm F F hF c.1 z) =
              ‖actualFixedNormalForm F G hG c.1 z -
                actualFixedNormalForm F F hF c.1 z‖ :=
              @dist_eq_norm (SymmetricSquare E →L[ℝ] normalSpace (I := I) F c.1)
                ContinuousLinearMap.toSeminormedAddCommGroup _ _
          _ < a / 4 := hform
      linarith
    have hnewgood := hball hnewball
    have hgeometry := actualFixedNormalForm_geometry F G hG c.1 z (hUchart hz) hnewgap
    exact ⟨hgeometry.2 hnewgood.1, fun hs ↦ hnewgood.2.2 (hgeometry.1.mpr hs)⟩
  choose U e he hU hcU hUcompact hUchart hUprojection hstable using hlocal
  obtain ⟨centers, hcover⟩ := hC.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcU ⟨x, hx⟩⟩)
  obtain ⟨e0, he0, he0le⟩ := finite_positive_common_lower_bound
    (fun c : centers ↦ e c.1) (fun c ↦ he c.1)
  let delta := min e0 (1 / 4 : ℝ)
  have hdelta : 0 < delta := lt_min he0 (by norm_num)
  refine ⟨centers, U, delta, hdelta,
    fun c ↦ ⟨hU c, hcU c, hUcompact c, hUchart c, hUprojection c⟩, ?_, ?_⟩
  · intro x hx
    simpa only [mem_iUnion, exists_prop] using hcover hx
  · intro G hG hclose x hx
    obtain ⟨c, hc, hxU⟩ : ∃ c ∈ centers, x ∈ U c := by
      simpa only [mem_iUnion, exists_prop] using hcover hx
    have hcclose := hclose c hc x (subset_closure hxU)
    exact hstable c G hG x (subset_closure hxU)
      (hcclose.1.trans_le (min_le_right _ _))
      (hcclose.2.trans_le ((min_le_left _ _).trans (he0le ⟨c, hc⟩)))

end GlobalEmbedding.Upgrade
