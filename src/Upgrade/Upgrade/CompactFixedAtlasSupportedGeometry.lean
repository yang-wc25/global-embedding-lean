import Upgrade.CompactOriginalC2Geometry
import Upgrade.CompactSupportedReserves

/-!
# Actual fixed-atlas forms in old normal coordinates

The source is the actual original atlas differential and the target is the
literal orthogonal projection onto one old actual normal space. Both are
geometric maps. Smallness of the actual normal projector makes the target
coordinate map injective, and the original C² bridge controls form errors
without any normal-identification choice or unsupported differentiation.
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

/-- The actual fixed-atlas second form projected to an old normal target. -/
def fixedAtlasNormalForm (A : BufferedAtlas M E) (F G : M → V)
    (center : M) (i : Fin A.count) (z : M) :
    SymmetricSquare E →L[ℝ] normalSpace (I := IM) F center :=
  (normalSpace (I := IM) F center).orthogonalProjectionOnto.comp
    (probeAtlasProjectedSecondForm A G i z)

/-- The exact source/target dictionary for the actual fixed-atlas form. -/
theorem fixedAtlasNormalForm_dictionary
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (center : M) (i : Fin A.count) (z : M) (hz : z ∈ (A.chart i).source) :
    (fixedAtlasNormalForm A F G center i z).toLinearMap =
      ((normalSpace (I := IM) F center).orthogonalProjectionOnto.comp
        (normalSpace (I := IM) G z).subtypeL).toLinearMap.comp
        ((show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) G z from trueSecondForm G hG z).comp
          (symmetricSquareLinearMap
            (probeAtlasInverseFrameEquiv A hA i z hz).toLinearMap)) := by
  rw [fixedAtlasNormalForm, probeAtlasProjectedSecondForm_eq_trueSecondForm A hA G hG i z hz]
  have he := congrArg ContinuousLinearMap.toLinearMap
    (probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i z hz)
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) G z := trueSecondForm G hG z
  apply LinearMap.ext
  intro q
  change (normalSpace (I := IM) F center).orthogonalProjectionOnto
      (B (symmetricSquareLinearMap (probeAtlasFrame A i z).toLinearMap q) : V) =
    (normalSpace (I := IM) F center).orthogonalProjectionOnto
      (B (symmetricSquareLinearMap (probeAtlasInverseFrameEquiv A hA i z hz).toLinearMap q) : V)
  exact congrArg (fun L : E →ₗ[ℝ] E ↦
    (normalSpace (I := IM) F center).orthogonalProjectionOnto
      (B (symmetricSquareLinearMap L q) : V)) he.symm

/-- Actual normal projection and actual invertible source coordinates preserve
supportedness and phase, and reflect surjectivity, whenever the normal gap is
less than one. The later map has no assumed rank or phase property. -/
theorem fixedAtlasNormalForm_geometry
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (center : M) (i : Fin A.count) (z : M) (hz : z ∈ (A.chart i).source)
    (hgap : ‖(normalSpace (I := IM) G z).starProjection -
      (normalSpace (I := IM) F center).starProjection‖ < 1) :
    (HasSupportedKernel (fixedAtlasNormalForm A F G center i z).toLinearMap ↔
      HasSupportedKernel (trueSecondForm G hG z)) ∧
    (LinearSecondFormPhaseRegular (fixedAtlasNormalForm A F G center i z).toLinearMap ↔
      LinearSecondFormPhaseRegular
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) G z from trueSecondForm G hG z)) ∧
    (Function.Surjective (fixedAtlasNormalForm A F G center i z) →
      Function.Surjective (trueSecondForm G hG z)) := by
  let j := (normalSpace (I := IM) F center).orthogonalProjectionOnto.comp
    (normalSpace (I := IM) G z).subtypeL
  have hj : Function.Injective j := normal_coordinate_injective _ _ hgap
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) G z := trueSecondForm G hG z
  let e := probeAtlasInverseFrameEquiv A hA i z hz
  have hdict := fixedAtlasNormalForm_dictionary A hA F G hG center i z hz
  change (fixedAtlasNormalForm A F G center i z).toLinearMap =
    j.toLinearMap.comp (B.comp (symmetricSquareLinearMap e.toLinearMap)) at hdict
  refine ⟨?_, ?_, ?_⟩
  · rw [hdict, hasSupportedKernel_postcomp_iff _ _ hj]
    exact hasSupportedKernel_source_coordinates_iff B e
  · rw [hdict, linearSecondFormPhaseRegular_postcomp_iff _ _ hj]
    exact linearSecondFormPhaseRegular_source_coordinates_iff B e
  · intro honto v
    obtain ⟨q, hq⟩ := honto (j v)
    refine ⟨symmetricSquareLinearMap e.toLinearMap q, hj ?_⟩
    have hqe := congrArg (fun T : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F center ↦ T q)
      hdict
    exact hqe.symm.trans hq

/-- At its old center the normal projection is the identity on the original
normal space, so only the actual invertible source frame remains. -/
theorem fixedAtlasNormalForm_self
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    (fixedAtlasNormalForm A F F x i x).toLinearMap =
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x).comp
        (symmetricSquareLinearMap (probeAtlasInverseFrameEquiv A hA i x hx).toLinearMap) := by
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  let e := probeAtlasInverseFrameEquiv A hA i x hx
  have hdict := fixedAtlasNormalForm_dictionary A hA F F hF x i x hx
  apply LinearMap.ext
  intro q
  have h := congrArg (fun L : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x ↦ L q) hdict
  change fixedAtlasNormalForm A F F x i x q =
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
      (B (symmetricSquareLinearMap e.toLinearMap q) : V) at h
  exact h.trans ((normalSpace (I := IM) F x).orthogonalProjectionOnto_mem_subspace_eq_self
    (B (symmetricSquareLinearMap e.toLinearMap q)))

/-- A literal fixed normal projection is contractive. Hence the form error
needed by supported-kernel protection is controlled by the actual fixed-atlas
projected-form error already obtained from the original C² norm. -/
theorem fixedAtlasNormalForm_sub_norm_le
    (A : BufferedAtlas M E) (F G : M → V) (center : M) (i : Fin A.count) (z : M) :
    ‖fixedAtlasNormalForm A F G center i z - fixedAtlasNormalForm A F F center i z‖ ≤
      ‖probeAtlasProjectedSecondForm A G i z - probeAtlasProjectedSecondForm A F i z‖ := by
  rw [fixedAtlasNormalForm, fixedAtlasNormalForm, ← ContinuousLinearMap.comp_sub]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right
      (Submodule.orthogonalProjectionOnto_norm_le _) (norm_nonneg _)).trans_eq (one_mul _))

end GlobalEmbedding.Upgrade
