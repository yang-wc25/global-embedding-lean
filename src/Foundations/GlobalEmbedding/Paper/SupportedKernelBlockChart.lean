import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!+# Actual kernel block coordinates for the supported locus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1006 and 1018–1022. In a fixed actual product decomposition, invert the right block
of the actual operator. Its kernel is precisely the graph of the resulting map. Native inverse
and composition calculus give the actual kernel differential and an explicit right inverse.
This is a chart provider, not an assumed Grassmannian or supported-locus geometry theorem.
-/

noncomputable section

open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The left block of the actual operator, as a continuous linear map on operators.
Source: `prop:supported-rank`, the fixed kernel/complement splitting. -/
def supportedKernelLeftBlock : ((E × F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ E (E × F) F).flip (ContinuousLinearMap.inl ℝ E F)

/-- The right block of the actual operator, with the original codomain.
Source: `prop:supported-rank`, the invertible complement block. -/
def supportedKernelRightBlock : ((E × F) →L[ℝ] F) →L[ℝ] (F →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ F (E × F) F).flip (ContinuousLinearMap.inr ℝ E F)

/-- The actual kernel graph map, using the native totalized operator inverse.
Its exact kernel meaning is proved when the actual right block is invertible.
Source: `prop:supported-rank`, kernel graph coordinates. -/
def supportedKernelBlockGraph (B : (E × F) →L[ℝ] F) : E →L[ℝ] F :=
  -((supportedKernelRightBlock B).inverse.comp (supportedKernelLeftBlock B))

/-- The two actual blocks reconstruct the original operator on every input.
Source: `prop:supported-rank`, the fixed product coordinates. -/
theorem supportedKernel_blocks_apply (B : (E × F) →L[ℝ] F) (u : E) (v : F) :
    B (u, v) = supportedKernelLeftBlock B u + supportedKernelRightBlock B v := by
  change B (u, v) = B (u, 0) + B (0, v)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- With its actual right block invertible, the actual kernel is exactly this graph.
Proof: solve the block equation `C u + A v = 0` using the genuine inverse of `A`.
Source: `prop:supported-rank`, local kernel graph. -/
theorem supportedKernel_mem_kernel_iff (B : (E × F) →L[ℝ] F) (e : F ≃L[ℝ] F)
    (hA : supportedKernelRightBlock B = (e : F →L[ℝ] F)) (u : E) (v : F) :
    B (u, v) = 0 ↔ v = supportedKernelBlockGraph B u := by
  rw [supportedKernel_blocks_apply, hA]
  simp only [supportedKernelBlockGraph, hA, ContinuousLinearMap.inverse_equiv,
    neg_apply, ContinuousLinearMap.comp_apply]
  constructor
  · intro h
    apply e.injective
    simpa using (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h))
  · intro h
    rw [h]
    simp

/-- Native inverse calculus makes the actual block graph smooth near every invertible block.
Source: `prop:supported-rank`, smoothness of the onto kernel map. -/
theorem supportedKernelBlockGraph_contDiffAt [CompleteSpace F]
    (B : (E × F) →L[ℝ] F) (e : F ≃L[ℝ] F)
    (hA : supportedKernelRightBlock B = (e : F →L[ℝ] F)) :
    ContDiffAt ℝ ∞ (supportedKernelBlockGraph (E := E) (F := F)) B := by
  have hI : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (supportedKernelRightBlock B) := by
    rw [hA]
    exact contDiffAt_map_inverse e
  exact ((hI.comp B (supportedKernelRightBlock (E := E) (F := F)).contDiff.contDiffAt).clm_comp
    (supportedKernelLeftBlock (E := E) (F := F)).contDiff.contDiffAt).neg

/-- At a base kernel splitting, the actual derivative is `Δ ↦ -A⁻¹ Δ|E`.
Proof: differentiate the native inverse/composition expression. The derivative of the inverse
is multiplied by the zero left block, so that term vanishes without an inverse-derivative
assumption. Source: `prop:supported-rank`, equation (9.4) before legal specialization. -/
theorem supportedKernelBlockGraph_hasFDerivAt [CompleteSpace F]
    (B : (E × F) →L[ℝ] F) (e : F ≃L[ℝ] F)
    (hA : supportedKernelRightBlock B = (e : F →L[ℝ] F))
    (hC : supportedKernelLeftBlock B = 0) :
    HasFDerivAt (supportedKernelBlockGraph (E := E) (F := F))
      (-((ContinuousLinearMap.compL ℝ E F F (e.symm : F →L[ℝ] F)).comp
        supportedKernelLeftBlock)) B := by
  have hI : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (supportedKernelRightBlock B) := by
    rw [hA]
    exact contDiffAt_map_inverse e
  have hi := (hI.comp B
    (supportedKernelRightBlock (E := E) (F := F)).contDiff.contDiffAt).differentiableAt
    (by simp)
  have hd := (hi.hasFDerivAt.clm_comp
    (supportedKernelLeftBlock (E := E) (F := F)).hasFDerivAt).neg
  simpa [supportedKernelBlockGraph, Function.comp_def, hA, hC] using! hd

/-- The actual kernel differential is onto, with an explicit perturbation of the left block.
Proof: lift `L` by `Δ(u,v)=-A(L u)`. This is the genuine kernel-map submersion, not a supplied
rank premise. Source: `prop:supported-rank`, smooth kernel projection from onto operators. -/
theorem supportedKernelBlockGraph_derivative_surjective (e : F ≃L[ℝ] F) :
    Function.Surjective
      (-((ContinuousLinearMap.compL ℝ E F F (e.symm : F →L[ℝ] F)).comp
        (supportedKernelLeftBlock (E := E) (F := F)))) := by
  intro L
  refine ⟨-((e : F →L[ℝ] F).comp L).comp (ContinuousLinearMap.fst ℝ E F), ?_⟩
  ext u
  simp [supportedKernelLeftBlock]

end GlobalEmbedding.Paper
