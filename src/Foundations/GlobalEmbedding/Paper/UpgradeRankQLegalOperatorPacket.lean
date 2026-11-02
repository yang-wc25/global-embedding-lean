import GlobalEmbedding.Paper.UpgradeRankQPointwiseLegalSpan
import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite actual legal operator packets at an original rank-q second form

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:upgrade`,
lines 1053–1057. This is only a finite operator packet. Actual manifold-local waves,
cutoffs, distant-point support, Schur/probe incidence and the original upgrade
remain obligations of the parent. DAG: `upgrade-rank-q-finite-legal-operator-packet`.
-/

noncomputable section

open Module
open scoped BigOperators

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- Original rank-q data produce n actual original legal operator columns and their
literal finite parameter sum. The genuine normal block, using projection onto the
SAME actual range-perpendicular line after restriction to the SAME actual kernel,
is differentiable at zero and has surjective derivative.

Proof: use the accepted original pointwise theorem for the actual dimensions,
every-good legal-space identity and full raw span. Native Basis.ofSpan selects a
basis INSIDE that raw generating set; native index equivalence reindexes it by
Fin n. Choose its actual good covectors and normal-line vectors. The original
rank-one operators on the original quotient give the finite CLM packet. Their
actual projected restrictions equal the selected basis columns, since projection
fixes each chosen normal-line vector. The old operator kills its actual kernel,
so its normal-block family is the native continuous basis-synthesis map. That
map has its genuine derivative equal to itself and is surjective. No desired
basis, rank, span, smooth-wave or parameter-surjectivity hypothesis is assumed.
Source: original main.tex1053–1057. -/
theorem upgradeRankQ_exists_legal_operator_packet
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →L[ℝ] W)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap)
    (hn : 3 ≤ finrank ℝ V)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1)
    (hrank : finrank ℝ B.toLinearMap.range = finrank ℝ V * (finrank ℝ V - 1) / 2) :
    let K := B.toLinearMap.ker
    let L := B.toLinearMap.rangeᗮ
    ∃ ξ : Fin (finrank ℝ V) → V →ₗ[ℝ] ℝ,
      ∃ ν : Fin (finrank ℝ V) → L,
        (∀ i, LinearSecondFormGoodCovector B.toLinearMap (ξ i) ∧
          (ν i : W) ∈ supportedRankLegalValueSpace B.toLinearMap (ξ i)) ∧
        ∃ P : (Fin (finrank ℝ V) → ℝ) →L[ℝ] (SymmetricSquare V →L[ℝ] W),
          (∀ t, P t = ∑ i, t i •
            (supportedRankLegalVariation (ξ i) (ν i : W)).toContinuousLinearMap) ∧
          let R : (Fin (finrank ℝ V) → ℝ) → (K →L[ℝ] L) := fun t ↦
            L.orthogonalProjectionOnto.comp ((B + P t).comp K.subtypeL)
          DifferentiableAt ℝ R 0 ∧ Function.Surjective (fderiv ℝ R 0) := by
  classical
  dsimp only
  let K := B.toLinearMap.ker
  let L := B.toLinearMap.rangeᗮ
  -- Cache the existing native operator parents before forming nested CLMs.
  let : NormedAddCommGroup (K →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (K →L[ℝ] L) := inferInstance
  obtain ⟨hdK, hdL, hlegal, hraw⟩ :=
    upgradeRankQ_pointwise_legal_span B.toLinearMap hphase hn hW hrank
  let S : Set (K →ₗ[ℝ] L) :=
    {f | ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
      ∃ ν : L, f = ((supportedRankCovectorSquare ξ).domRestrict K).smulRight ν}
  have hS : Submodule.span ℝ S = ⊤ := hraw
  have hdH : finrank ℝ (K →ₗ[ℝ] L) = finrank ℝ V := by
    rw [Module.finrank_linearMap]
    change finrank ℝ B.toLinearMap.ker * finrank ℝ B.toLinearMap.rangeᗮ = _
    rw [hdK, hdL, mul_one]
  let b0 := Basis.ofSpan hS.ge
  let bf := Module.finBasisOfFinrankEq ℝ (K →ₗ[ℝ] L) hdH
  let b : Basis (Fin (finrank ℝ V)) ℝ (K →ₗ[ℝ] L) :=
    b0.reindex (b0.indexEquiv bf)
  have hmem (i : Fin (finrank ℝ V)) : b i ∈ S := by
    dsimp only [b]
    rw [Basis.reindex_apply]
    exact Basis.ofSpan_subset hS.ge ⟨(b0.indexEquiv bf).symm i, rfl⟩
  have hw : ∀ i : Fin (finrank ℝ V),
      ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
        ∃ ν : L, b i = ((supportedRankCovectorSquare ξ).domRestrict K).smulRight ν :=
    fun i ↦ hmem i
  choose ξ hgood ν hb using hw
  let E : (K →ₗ[ℝ] L) ≃ₗ[ℝ] (K →L[ℝ] L) := LinearMap.toContinuousLinearMap
  let bc := b.map E
  let C : (Fin (finrank ℝ V) → ℝ) →L[ℝ] (K →L[ℝ] L) :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (bc i)
  have hCt (t : Fin (finrank ℝ V) → ℝ) : C t = ∑ i, t i • bc i := by
    simp only [C, sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  have hCs : Function.Surjective C := by
    intro y
    refine ⟨bc.equivFun y, ?_⟩
    rw [hCt]
    exact bc.sum_equivFun y
  let dotB : Fin (finrank ℝ V) → SymmetricSquare V →L[ℝ] W := fun i ↦
    (supportedRankLegalVariation (ξ i) (ν i : W)).toContinuousLinearMap
  let P : (Fin (finrank ℝ V) → ℝ) →L[ℝ] (SymmetricSquare V →L[ℝ] W) :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (dotB i)
  have hPt (t : Fin (finrank ℝ V) → ℝ) : P t = ∑ i, t i • dotB i := by
    simp only [P, sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  have hblock (i : Fin (finrank ℝ V)) :
      L.orthogonalProjectionOnto.comp ((dotB i).comp K.subtypeL) = bc i := by
    have hbi : bc i = (b i).toContinuousLinearMap := Basis.map_apply b E i
    rw [hbi]
    apply ContinuousLinearMap.ext
    intro k
    change L.orthogonalProjectionOnto
      (supportedRankCovectorSquare (ξ i) (k : SymmetricSquare V) • (ν i : W)) = (b i) k
    rw [hb i]
    change L.orthogonalProjectionOnto
      (supportedRankCovectorSquare (ξ i) (k : SymmetricSquare V) • (ν i : W)) =
        supportedRankCovectorSquare (ξ i) (k : SymmetricSquare V) • ν i
    rw [map_smul, L.orthogonalProjectionOnto_mem_subspace_eq_self]
  let R : (Fin (finrank ℝ V) → ℝ) → (K →L[ℝ] L) := fun t ↦
    L.orthogonalProjectionOnto.comp ((B + P t).comp K.subtypeL)
  have hR : R = C := by
    funext t
    rw [hCt]
    apply ContinuousLinearMap.ext
    intro k
    change L.orthogonalProjectionOnto ((B + P t) (k : SymmetricSquare V)) =
      (∑ i, t i • bc i) k
    have hk : B (k : SymmetricSquare V) = 0 := k.property
    rw [add_apply, hk, zero_add, hPt]
    simp only [sum_apply, smul_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun v : L ↦ t i • v) (DFunLike.congr_fun (hblock i) k)
  have hderiv : HasFDerivAt R C 0 := by
    rw [hR]
    exact C.hasFDerivAt
  refine ⟨ξ, ν, ?_, P, hPt, hderiv.differentiableAt, ?_⟩
  · intro i
    refine ⟨hgood i, ?_⟩
    rw [hlegal (ξ i) (hgood i)]
    exact (ν i).property
  · rw [hderiv.fderiv]
    exact hCs

#print axioms upgradeRankQ_exists_legal_operator_packet

end GlobalEmbedding.Paper
