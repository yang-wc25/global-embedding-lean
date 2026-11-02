import GlobalEmbedding.Paper.SupportedKernelBlockChart
import GlobalEmbedding.Paper.SupportedRankKernelComplementInverse

/-!
# Actual kernel-chart specialization and rank-one variation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
equation (9.4), lines 1014–1022. The generic block derivative is the accepted W3
provider. This module only changes to the actual kernel/complement coordinates,
applies the chain rule, and specializes its value to actual rank-one columns.
-/

noncomputable section
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {S W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The native actual decomposition `S=ker B⊕(ker B)⊥`.
Source: `prop:supported-rank`, the fixed kernel graph chart of equation (9.4). -/
def supportedRankKernelCoordinates (B : S →L[ℝ] W) : (B.ker × B.kerᗮ) ≃L[ℝ] S :=
  (B.ker.prodEquivOfIsCompl B.kerᗮ B.ker.isCompl_orthogonal).toContinuousLinearEquiv

/-- The actual coordinates are the literal sum of the two included vectors.
Source: `prop:supported-rank`, orthogonal kernel/complement coordinates. -/
@[simp] theorem supportedRankKernelCoordinates_apply (B : S →L[ℝ] W)
    (q : B.ker) (z : B.kerᗮ) :
    supportedRankKernelCoordinates B (q, z) = (q : S) + (z : S) := rfl

/-- Change the actual operator to the native block chart, using the genuine inverse
of its fixed complement restriction. Source: `prop:supported-rank`, equation (9.4). -/
def supportedRankKernelChartOperator (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    (S →L[ℝ] W) →L[ℝ] ((B.ker × B.kerᗮ) →L[ℝ] B.kerᗮ) :=
  ((ContinuousLinearMap.compL ℝ (B.ker × B.kerᗮ) S B.kerᗮ).flip
    (supportedRankKernelCoordinates B : (B.ker × B.kerᗮ) →L[ℝ] S)).comp
      (ContinuousLinearMap.compL ℝ S W B.kerᗮ
        ((supportedRankKernelComplementEquiv B hB).symm : W →L[ℝ] B.kerᗮ))

/-- The base operator has zero left block in its actual kernel coordinates.
Source: `prop:supported-rank`, kernel graph based at `K=ker B`. -/
theorem supportedRankKernelChartOperator_left (B : S →L[ℝ] W)
    (hB : Function.Surjective B) :
    supportedKernelLeftBlock (supportedRankKernelChartOperator B hB B) = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  change (supportedRankKernelComplementEquiv B hB).symm (B ((q : S) + 0)) = 0
  have hq : B (q : S) = 0 := q.property
  rw [add_zero, hq, map_zero]

/-- The base operator has the identity right block after the actual inverse restriction.
Source: `prop:supported-rank`, the invertible complement block in equation (9.4). -/
theorem supportedRankKernelChartOperator_right (B : S →L[ℝ] W)
    (hB : Function.Surjective B) :
    supportedKernelRightBlock (supportedRankKernelChartOperator B hB B) =
      ContinuousLinearMap.id ℝ B.kerᗮ := by
  apply ContinuousLinearMap.ext
  intro z
  change (supportedRankKernelComplementEquiv B hB).symm (B (0 + (z : S))) = z
  rw [zero_add, ← supportedRankKernelComplementEquiv_apply B hB z]
  exact (supportedRankKernelComplementEquiv B hB).symm_apply_apply z

/-- The actual local kernel graph, defined through the sole native block-graph provider.
Source: `prop:supported-rank`, equation (9.4). -/
def supportedRankKernelGraph (B : S →L[ℝ] W) (hB : Function.Surjective B)
    (C : S →L[ℝ] W) : B.ker →L[ℝ] B.kerᗮ :=
  supportedKernelBlockGraph (supportedRankKernelChartOperator B hB C)

/-- The explicit actual derivative `Δ↦-A⁻¹Δ|K`, with no derivative premise.
Source: `prop:supported-rank`, equation (9.4) before substituting the legal column. -/
def supportedRankKernelGraphDerivative (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    (S →L[ℝ] W) →L[ℝ] (B.ker →L[ℝ] B.kerᗮ) :=
  -((ContinuousLinearMap.compL ℝ B.ker W B.kerᗮ
      ((supportedRankKernelComplementEquiv B hB).symm : W →L[ℝ] B.kerᗮ)).comp
    ((ContinuousLinearMap.compL ℝ B.ker S W).flip B.ker.subtypeL))

/-- The actual kernel-map derivative follows by applying the chain rule to W3's
accepted block derivative and the fixed actual coordinate map. No inverse calculus
is reproved here. Source: `prop:supported-rank`, equation (9.4). -/
theorem supportedRankKernelGraph_hasFDerivAt (B : S →L[ℝ] W)
    (hB : Function.Surjective B) :
    HasFDerivAt (supportedRankKernelGraph B hB) (supportedRankKernelGraphDerivative B hB) B := by
  have hc : HasFDerivAt
      (fun C : S →L[ℝ] W ↦ supportedRankKernelChartOperator B hB C)
      (supportedRankKernelChartOperator B hB) B :=
    (supportedRankKernelChartOperator B hB).hasFDerivAt
  have hb := supportedKernelBlockGraph_hasFDerivAt
    (supportedRankKernelChartOperator B hB B) (ContinuousLinearEquiv.refl ℝ B.kerᗮ)
    (supportedRankKernelChartOperator_right B hB)
    (supportedRankKernelChartOperator_left B hB)
  have hd := HasFDerivAt.comp (𝕜 := ℝ)
    (f := fun C : S →L[ℝ] W ↦ supportedRankKernelChartOperator B hB C)
    (g := supportedKernelBlockGraph (E := B.ker) (F := B.kerᗮ)) B hb hc
  convert hd using 1
  · rfl
  · ext Δ q
    simp [supportedRankKernelGraphDerivative, supportedRankKernelChartOperator,
      supportedKernelLeftBlock, supportedRankKernelCoordinates]

/-- The differential on an actual rank-one column is its literal inverse-restriction value.
Source: `prop:supported-rank`, substitution of `ν⊗ξ²` in equation (9.4). -/
theorem supportedRankKernelGraph_fderiv_rankOne (B : S →L[ℝ] W)
    (hB : Function.Surjective B) (l : S →L[ℝ] ℝ) (ν : W) (q : B.ker) :
    (fderiv ℝ (supportedRankKernelGraph B hB) B) (l.smulRight ν) q =
      -(l q • (supportedRankKernelComplementEquiv B hB).symm ν) := by
  rw [(supportedRankKernelGraph_hasFDerivAt B hB).fderiv]
  simp [supportedRankKernelGraphDerivative]

/-- Whenever the actual right block is invertible, the graph is precisely the
kernel of the original operator in the fixed actual decomposition.
Source: `prop:supported-rank`, the literal kernel graph used in equation (9.4). -/
theorem supportedRankKernelGraph_mem_kernel_iff (B : S →L[ℝ] W)
    (hB : Function.Surjective B) (C : S →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) (q : B.ker) (z : B.kerᗮ) :
    C ((q : S) + (z : S)) = 0 ↔ z = supportedRankKernelGraph B hB C q := by
  have hzero : C ((q : S) + (z : S)) = 0 ↔
      supportedRankKernelChartOperator B hB C (q, z) = 0 := by
    change C ((q : S) + (z : S)) = 0 ↔
      (supportedRankKernelComplementEquiv B hB).symm (C ((q : S) + (z : S))) = 0
    exact ((supportedRankKernelComplementEquiv B hB).symm.map_eq_zero_iff).symm
  rw [hzero]
  exact supportedKernel_mem_kernel_iff _ e hA q z

/-- The actual graph is smooth at the base onto operator, by the sole block-chart provider.
Source: `prop:supported-rank`, smooth kernel graph in the actual ambient operator space. -/
theorem supportedRankKernelGraph_contDiffAt (B : S →L[ℝ] W)
    (hB : Function.Surjective B) : ContDiffAt ℝ ∞ (supportedRankKernelGraph B hB) B := by
  have hc : ContDiffAt ℝ ∞
      (fun C : S →L[ℝ] W ↦ supportedRankKernelChartOperator B hB C) B :=
    by
      change ContDiffAt ℝ ∞ (fun C : S →L[ℝ] W ↦
        ((supportedRankKernelComplementEquiv B hB).symm : W →L[ℝ] B.kerᗮ).comp
          (C.comp (supportedRankKernelCoordinates B : (B.ker × B.kerᗮ) →L[ℝ] S))) B
      exact (contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)).contDiffAt
  have hb := supportedKernelBlockGraph_contDiffAt
    (supportedRankKernelChartOperator B hB B) (ContinuousLinearEquiv.refl ℝ B.kerᗮ)
    (supportedRankKernelChartOperator_right B hB)
  have hh := ContDiffAt.comp (𝕜 := ℝ)
    (f := fun C : S →L[ℝ] W ↦ supportedRankKernelChartOperator B hB C)
    (g := supportedKernelBlockGraph (E := B.ker) (F := B.kerᗮ)) B hb hc
  exact hh

/-- Substituting the genuine adjoint equation gives the actual inverse-Gram expression.
The displayed adjoint equation is later supplied by its proved actual inverse, not
by an original-target premise. Source: `prop:supported-rank`, equation (9.4). -/
theorem supportedRankKernelGraph_fderiv_rankOne_adjoint [FiniteDimensional ℝ W]
    (B : S →L[ℝ] W) (hB : Function.Surjective B) (l : S →L[ℝ] ℝ)
    (ν : W) (z : B.kerᗮ) (hν : B.adjoint ν = (z : S)) (q : B.ker) :
    (fderiv ℝ (supportedRankKernelGraph B hB) B) (l.smulRight ν) q =
      -(l q • ((supportedRankKernelComplementMap B).adjoint.comp
        (supportedRankKernelComplementMap B)).inverse z) := by
  have hA : (supportedRankKernelComplementMap B).adjoint ν = z := by
    unfold supportedRankKernelComplementMap
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    change B.kerᗮ.orthogonalProjectionOnto (B.adjoint ν) = z
    rw [hν]
    simp
  rw [supportedRankKernelGraph_fderiv_rankOne,
    supportedRankKernelComplementEquiv_symm_gram B hB ν, hA]

#print axioms supportedRankKernelCoordinates
#print axioms supportedRankKernelCoordinates_apply
#print axioms supportedRankKernelChartOperator
#print axioms supportedRankKernelChartOperator_left
#print axioms supportedRankKernelChartOperator_right
#print axioms supportedRankKernelGraph
#print axioms supportedRankKernelGraphDerivative
#print axioms supportedRankKernelGraph_hasFDerivAt
#print axioms supportedRankKernelGraph_fderiv_rankOne
#print axioms supportedRankKernelGraph_mem_kernel_iff
#print axioms supportedRankKernelGraph_contDiffAt
#print axioms supportedRankKernelGraph_fderiv_rankOne_adjoint

end GlobalEmbedding.Paper
