import GlobalEmbedding.Paper.CovectorKernelProjectionProperties
import GlobalEmbedding.Paper.SymmetricSquareSubspaceIsometry
import GlobalEmbedding.Paper.SmoothSymmetricSquareTransport

open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance trialSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance trialSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- An actual symmetric-kernel vector can be moved continuously in the fixed
ambient quotient by the actual rank-one kernel projection. Each nearby trial is
the inclusion of a vector in the actual nearby kernel square with exactly the
same norm.

Proof: apply the accepted exact smooth symmetric-square transport to the kernel
projection field. Restrict and corestrict the actual projection to obtain a map
between the literal kernels. Functoriality and the proved subspace isometry give
the preimage and its norm. Source: `defn:phase`, maximum of hyperplane minima. -/
theorem covector_kernel_trial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : E) (ξ0 : E →L[ℝ] ℝ) (h0 : ξ0 v ≠ 0) (z0 : SymmetricSquare ξ0.ker) :
    let a := fun ξ : E →L[ℝ] ℝ ↦ symmetricSquareMapL (covectorKernelProjection v ξ)
      (symmetricSquareMapL ξ0.ker.subtypeL z0)
    ContinuousAt a ξ0 ∧ a ξ0 = symmetricSquareMapL ξ0.ker.subtypeL z0 ∧
    ∀ ξ : E →L[ℝ] ℝ, ξ v ≠ 0 → ∃ z : SymmetricSquare ξ.ker,
      symmetricSquareMapL ξ.ker.subtypeL z = a ξ ∧ ‖z‖ = ‖a ξ‖ := by
  let a := fun ξ : E →L[ℝ] ℝ ↦ symmetricSquareMapL (covectorKernelProjection v ξ)
    (symmetricSquareMapL ξ0.ker.subtypeL z0)
  have hproj := covector_kernel_projection_properties v ξ0 h0
  have hs := (smooth_symmetric_square_transport (E := E) (F := E) (n := ∞)).continuous
  have ha : ContinuousAt a ξ0 :=
    (hs.continuousAt.comp hproj.1).clm_apply continuousAt_const
  have hfix : (covectorKernelProjection v ξ0).comp ξ0.ker.subtypeL = ξ0.ker.subtypeL := by
    ext w
    exact hproj.2.2 ξ0 w w.property
  have ha0 : a ξ0 = symmetricSquareMapL ξ0.ker.subtypeL z0 := by
    change symmetricSquareMapL (covectorKernelProjection v ξ0)
      (symmetricSquareMapL ξ0.ker.subtypeL z0) = _
    simp only [symmetricSquareMapL_apply, symmetricSquareMap_comp, hfix]
  refine ⟨ha, ha0, ?_⟩
  intro ξ hξ
  let L := (covectorKernelProjection v ξ).comp ξ0.ker.subtypeL
  have hL : ∀ w, L w ∈ ξ.ker := by
    intro w
    change ξ (covectorKernelProjection v ξ w) = 0
    exact hproj.2.1 ξ hξ w
  let T : ξ0.ker →L[ℝ] ξ.ker := L.codRestrict ξ.ker hL
  let z := symmetricSquareMapL T z0
  have hcomp : ξ.ker.subtypeL.comp T =
      (covectorKernelProjection v ξ).comp ξ0.ker.subtypeL := rfl
  have hz : symmetricSquareMapL ξ.ker.subtypeL z = a ξ := by
    change symmetricSquareMapL ξ.ker.subtypeL (symmetricSquareMapL T z0) =
      symmetricSquareMapL (covectorKernelProjection v ξ) (symmetricSquareMapL ξ0.ker.subtypeL z0)
    simp only [symmetricSquareMapL_apply, symmetricSquareMap_comp, hcomp]
  refine ⟨z, hz, ?_⟩
  exact (symmetric_square_subspace_isometry ξ.ker z).symm.trans (congrArg norm hz)

end GlobalEmbedding.Paper
