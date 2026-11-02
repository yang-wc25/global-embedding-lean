import Upgrade.CompactFixedAtlasSupportedGeometry

/-!
# Original C² protection of the actual nonsupported compact region

Every normal target is chosen from one actual old point. A finite compact
cover and genuine open nonsupported-operator balls are constructed, then the
proved original C² bounds supply their projection and form errors. Later maps
are not assumed full rank, nonsupported, phase regular, or to have a selected
normal identification. The empty compact region uses the same construction.
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
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A compact actual full-rank nonsupported region has one genuine original
C² protection budget. This closes the earlier explicit projection/coefficient
consumer using the literal fixed original atlas, including source-frame change. -/
theorem exists_originalC2_nonsupported_reserve
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hgood : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x)) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ x ∈ C, Function.Surjective (trueSecondForm G hG x) ∧
        ¬ HasSupportedKernel (trueSecondForm G hG x) := by
  classical
  let J := Σ i : Fin A.count, ↥(C ∩ A.support i)
  let : ∀ i, CompactSpace ↥(C ∩ A.support i) := fun i ↦
    isCompact_iff_compactSpace.mp (hC.inter (hcompact i))
  let point : J → M := fun z ↦ z.2
  have hpoint : Continuous point := continuous_sigma_iff.mpr fun _ ↦ continuous_subtype_val
  let S : J → SymmetricSquare E →L[ℝ] V := fun z ↦
    probeAtlasProjectedSecondForm A F z.1 z.2
  have hS : Continuous S := continuous_sigma_iff.mpr fun i ↦
    ((continuousOn_probeAtlasProjectedSecondForm A hA F hF himm i).mono
      (fun _ hx ↦ hA.support_subset i hx.2)).domRestrict
  have hP : Continuous (fun z : J ↦ (normalSpace (I := IM) F (point z)).starProjection) :=
    (smooth_immersion_normal_projection F hF himm).continuous.comp hpoint
  have hlocal (p : J) : ∃ U : Set J, ∃ a > 0,
      IsOpen U ∧ p ∈ U ∧
      ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G) (z : J), z ∈ U →
        ‖(normalSpace (I := IM) G (point z)).starProjection -
          (normalSpace (I := IM) F (point z)).starProjection‖ < (1 / 4 : ℝ) →
        ‖probeAtlasProjectedSecondForm A G z.1 z.2 - S z‖ < a →
        Function.Surjective (trueSecondForm G hG (point z)) ∧
          ¬ HasSupportedKernel (trueSecondForm G hG (point z)) := by
    let D : J → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F (point p) :=
      fun z ↦ (normalSpace (I := IM) F (point p)).orthogonalProjectionOnto.comp (S z)
    have hD : Continuous D := continuous_const.clm_comp hS
    let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F (point p) := trueSecondForm F hF (point p)
    let frame := probeAtlasInverseFrameEquiv A hA p.1 p.2 (hA.support_subset p.1 p.2.property.2)
    have hself : (D p).toLinearMap = B.comp (symmetricSquareLinearMap frame.toLinearMap) :=
      fixedAtlasNormalForm_self A hA F hF p.1 p.2 (hA.support_subset p.1 p.2.property.2)
    have hDgood : D p ∈ {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F (point p) |
        Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap ∧
          ¬ HasSupportedKernel B.toLinearMap} := by
      refine ⟨?_, ?_, ?_⟩
      · change Function.Surjective (D p).toLinearMap
        rw [hself]
        exact (surjective_symmetricSquare_source_coordinates_iff B frame.toLinearEquiv).mpr
          (hgood (point p) p.2.property.1).1
      · rw [hself]
        exact (linearSecondFormPhaseRegular_source_coordinates_iff B frame).mpr
          (trueSecondForm_linearPhaseRegular F hF hphase (point p))
      · rw [hself, hasSupportedKernel_source_coordinates_iff B frame]
        exact (hgood (point p) p.2.property.1).2
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_operator_nonsupported _ hDgood
    let U : Set J := {z | dist (D z) (D p) < r / 4 ∧
      ‖(normalSpace (I := IM) F (point z)).starProjection -
        (normalSpace (I := IM) F (point p)).starProjection‖ < (1 / 2 : ℝ)}
    have hU : IsOpen U :=
      (isOpen_lt (hD.dist continuous_const) continuous_const).inter
        (isOpen_lt (hP.sub continuous_const).norm continuous_const)
    have hpU : p ∈ U := by
      change dist (D p) (D p) < r / 4 ∧ ‖(normalSpace (I := IM) F (point p)).starProjection -
        (normalSpace (I := IM) F (point p)).starProjection‖ < (1 / 2 : ℝ)
      simp only [dist_self, sub_self, norm_zero]
      exact ⟨by positivity, by norm_num⟩
    refine ⟨U, r / 4, by positivity, hU, hpU, ?_⟩
    intro G hG z hz hprojector hform
    have hnewgap : ‖(normalSpace (I := IM) G (point z)).starProjection -
        (normalSpace (I := IM) F (point p)).starProjection‖ < 1 := by
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (normalSpace (I := IM) G (point z)).starProjection
        (normalSpace (I := IM) F (point z)).starProjection
        (normalSpace (I := IM) F (point p)).starProjection
      have hold := hz.2
      linarith
    have hnewball : fixedAtlasNormalForm A F G (point p) z.1 z.2 ∈ Metric.ball (D p) r := by
      change dist (fixedAtlasNormalForm A F G (point p) z.1 z.2) (D p) < r
      have hstep : dist (fixedAtlasNormalForm A F G (point p) z.1 z.2) (D z) < r / 4 := by
        calc
          _ = ‖fixedAtlasNormalForm A F G (point p) z.1 z.2 - D z‖ :=
            @dist_eq_norm (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F (point p))
              ContinuousLinearMap.toSeminormedAddCommGroup _ _
          _ ≤ ‖probeAtlasProjectedSecondForm A G z.1 z.2 - S z‖ :=
            fixedAtlasNormalForm_sub_norm_le A F G (point p) z.1 z.2
          _ < r / 4 := hform
      have htri := dist_triangle (fixedAtlasNormalForm A F G (point p) z.1 z.2) (D z) (D p)
      have hbase := hz.1
      linarith
    have hnewgood := hball hnewball
    have hgeometry := fixedAtlasNormalForm_geometry A hA F G hG (point p) z.1 z.2
      (hA.support_subset z.1 z.2.property.2) hnewgap
    exact ⟨hgeometry.2.2 hnewgood.1, fun hs ↦ hnewgood.2.2 (hgeometry.1.mpr hs)⟩
  choose U a ha hU hpU hstable using hlocal
  obtain ⟨centers, hfinitecover⟩ := (isCompact_univ : IsCompact (univ : Set J))
    |>.elim_finite_subcover U hU (fun z _ ↦ mem_iUnion.mpr ⟨z, hpU z⟩)
  obtain ⟨d0, hd0, hd0le⟩ := finite_positive_common_lower_bound
    (fun p : centers ↦ a p.1) (fun p ↦ ha p.1)
  let d := min d0 (1 / 4 : ℝ)
  have hd : 0 < d := lt_min hd0 (by norm_num)
  obtain ⟨e, he, herr⟩ := exists_originalC2_normal_and_form_budget
    A hA hcompact hcover hdim F hF himm hphase hd
  refine ⟨e, he, ?_⟩
  intro G hG hbudget x hx
  obtain ⟨i, hxi⟩ := hcover x
  let z : J := ⟨i, x, hx, hxi⟩
  obtain ⟨p, hp, hzU⟩ : ∃ p ∈ centers, z ∈ U p := by
    simpa only [mem_iUnion, exists_prop] using hfinitecover (mem_univ z)
  exact hstable p G hG z hzU
    ((herr G hG hbudget).1 x |>.trans_le (min_le_right _ _))
    (((herr G hG hbudget).2 i x hxi).trans_le
      ((min_le_left _ _).trans (hd0le ⟨p, hp⟩)))

end GlobalEmbedding.Upgrade
