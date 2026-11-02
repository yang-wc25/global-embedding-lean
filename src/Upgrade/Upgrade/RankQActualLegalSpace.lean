import Upgrade.RankQActualSecondForm

/-!
# The accepted rank-q legal-space classification on the actual true form

This file only specializes `upgradeRankQ_pointwise_legal_span` to the
actual immersion, in order to use one fixed pre-probe local-wave packet.
-/

noncomputable section
open Manifold Module
open scoped ContDiff
namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- Exact native kernel, perpendicular range, and all legal value spaces of
the actual reference form. No incidence rank is assumed. -/
theorem rankQActual_dims_and_legal
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (himm : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2) :
    let B := rankQActualReference F hF x
    finrank ℝ B.ker = n ∧ finrank ℝ B.rangeᗮ = 1 ∧
      ∀ xi : TangentSpace I x →L[ℝ] ℝ, GoodCovector F hF x xi →
        supportedRankLegalValueSpace (trueSecondForm F hF x) xi.toLinearMap = B.rangeᗮ := by
  let : NormedAddCommGroup (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := operatorSquareNormed
  let : NormedSpace ℝ (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := squareNS _
  let : NormedAddCommGroup (normalSpace (I := I) F x) := Submodule.normedAddCommGroup _
  let : InnerProductSpace ℝ (normalSpace (I := I) F x) := inferInstance
  let B := rankQActualReference F hF x
  have hW : finrank ℝ (normalSpace (I := I) F x) = n * (n - 1) / 2 + 1 := by
    rw [immersion_normal_rank F x himm, finrank_euclideanSpace_fin, hN]
    have heq : n * (n + 1) = n * (n - 1) + 2 * n := by
      calc
        n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
        _ = n * (n - 1) + 2 * n := by ring
    omega
  have hphaseB : LinearSecondFormPhaseRegular B.toLinearMap := by
    obtain ⟨eta, heta⟩ := hphase x
    refine ⟨eta.toLinearMap, ?_, heta.2⟩
    intro hz
    apply heta.1
    apply DFunLike.ext
    intro a
    exact DFunLike.congr_fun hz a
  have hpointwise := upgradeRankQ_pointwise_legal_span
    (V := EuclideanSpace ℝ (Fin n)) (W := normalSpace (I := I) F x)
    B.toLinearMap hphaseB (by simpa using hn) (by simpa using hW)
    (by simpa only [B, rankQActualReference, finrank_euclideanSpace_fin] using! hrank)
  refine ⟨hpointwise.1.trans finrank_euclideanSpace_fin, hpointwise.2.1, ?_⟩
  intro xi hxi
  have hgood : LinearSecondFormGoodCovector B.toLinearMap xi.toLinearMap := by
    refine ⟨?_, hxi.2⟩
    intro hz
    apply hxi.1
    apply DFunLike.ext
    intro a
    exact DFunLike.congr_fun hz a
  exact hpointwise.2.2.1 xi.toLinearMap hgood

end GlobalEmbedding.Upgrade
