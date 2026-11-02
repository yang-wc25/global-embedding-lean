import Upgrade.RankQSchurRank
import Upgrade.RankQSchurDifferential
import GlobalEmbedding.Paper.UpgradeRankQDuplicatedPrincipalPacket

/-!
# Schur rank equations for the paper's actual second fundamental form

Both the source frame and normal identification are explicit in the actual
representative.  The rank identity is invariant under these honest linear
equivalences. Their derivatives are not silently discarded: smoothness and
quantitative bounds for a varying representative must refer to this whole
composition. In particular, a mere smooth choice of normal identifications
does not imply the C1 bound required by the incidence argument.
-/

noncomputable section
open Manifold Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- The original quotient-valued true second form, with its existing quotient norm. -/
def rankQActualReference (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M) :
    SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
  LinearMap.toContinuousLinearMap (trueSecondForm F hF x)

/-- Literal representative of a second actual map in fixed source and old-normal frames. -/
def rankQActualRepresentative
    (F G : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (x z : M)
    (sourceFrame : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] TangentSpace I z)
    (normalFrame : normalSpace (I := I) G z ≃ₗ[ℝ] normalSpace (I := I) F x) :
    SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
  LinearMap.toContinuousLinearMap
    (normalFrame.toLinearMap.comp ((trueSecondForm G hG z).comp
      (saturationSymmetricSquareEquiv sourceFrame).toLinearMap))

/-- Honest source and normal changes preserve the rank of the SAME actual form. -/
theorem rankQActualRepresentative_finrank_range
    (F G : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (x z : M)
    (sourceFrame : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] TangentSpace I z)
    (normalFrame : normalSpace (I := I) G z ≃ₗ[ℝ] normalSpace (I := I) F x) :
    finrank ℝ (rankQActualRepresentative F G hG x z sourceFrame normalFrame).range =
      finrank ℝ (trueSecondForm G hG z).range := by
  change finrank ℝ (normalFrame.toLinearMap.comp ((trueSecondForm G hG z).comp
    (saturationSymmetricSquareEquiv sourceFrame).toLinearMap)).range = _
  rw [LinearMap.range_comp, normalFrame.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (saturationSymmetricSquareEquiv sourceFrame).range]

/-- The literal Schur equation in this fixed actual chart is exactly rank q of G. -/
theorem rankQActualSchur_eq_zero_iff
    (F G : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (x z : M)
    (sourceFrame : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] TangentSpace I z)
    (normalFrame : normalSpace (I := I) G z ≃ₗ[ℝ] normalSpace (I := I) F x)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (hA : (rankQBlockA (rankQActualReference F hF x)
      (rankQActualRepresentative F G hG x z sourceFrame normalFrame)).IsInvertible) :
    rankQSchur (rankQActualReference F hF x)
      (rankQActualRepresentative F G hG x z sourceFrame normalFrame) = 0 ↔
      finrank ℝ (trueSecondForm G hG z).range = n * (n - 1) / 2 := by
  rw [rankQSchur_eq_zero_iff_rank _ _ hA,
    rankQActualRepresentative_finrank_range]
  exact hrank ▸ Iff.rfl

/-- Actual original rank-q geometry gives exactly n independent Schur equations. -/
theorem rankQActualSchur_output_finrank
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1) (x : M)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2) :
    let B := rankQActualReference F hF x
    finrank ℝ (B.ker →L[ℝ] B.rangeᗮ) = n := by
  let B := rankQActualReference F hF x
  have hW : finrank ℝ (normalSpace (I := I) F x) = n * (n - 1) / 2 + 1 := by
    rw [immersion_normal_rank F x (himm x), finrank_euclideanSpace_fin, hN]
    have heq : n * (n + 1) = n * (n - 1) + 2 * n := by
      calc
        n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
        _ = n * (n - 1) + 2 * n := by ring
    omega
  have hp : LinearSecondFormPhaseRegular B.toLinearMap := by
    obtain ⟨xi, hxi⟩ := hphase x
    refine ⟨xi.toLinearMap, ?_, hxi.2⟩
    intro he
    apply hxi.1
    exact DFunLike.ext _ _ (fun v ↦ DFunLike.congr_fun he v)
  have hd := upgradeRankQ_pointwise_legal_span B.toLinearMap hp
    (by simpa using hn) (by simpa using hW) (by simpa only [B, rankQActualReference, finrank_euclideanSpace_fin] using! hrank)
  change finrank ℝ (B.ker →L[ℝ] B.rangeᗮ) = n
  rw [← LinearMap.toContinuousLinearMap.finrank_eq, Module.finrank_linearMap,
    hd.1, hd.2.1, mul_one, finrank_euclideanSpace_fin]

end GlobalEmbedding.Upgrade
