import NormalPolar.CompressionQuantitative
import NormalPolar.Smooth
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Native response of the same actual old-normal inverse square root

The fixed old-normal compression is applied to the one explicit analytic
series at the actual squared projection defect. Differentiability, its
chain rule, the Sylvester identity and self-adjointness of its native
response are derived here. None is an independent response premise.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private noncomputable local instance compressionResponseAmbientSemi :
    SeminormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance compressionResponseAmbientNorm :
    NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance compressionResponseAmbientSpace :
    NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance compressionResponseFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance compressionResponseFiberNorm (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance compressionResponseFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

/-- The same explicit compression, written as a function of its actual
ambient projection input. Substituting L.starProjection is definitionally
the already constructed actualNormalInverseSqrt K L. -/
def actualNormalInverseSqrtFromProjection (K : Submodule ℝ V) (R : V →L[ℝ] V) : K →L[ℝ] K :=
  normalProjectionCompression K (actualInvSqrt (projectionDefect K.starProjection R))

@[simp] theorem actualNormalInverseSqrtFromProjection_starProjection
    (K L : Submodule ℝ V) :
    actualNormalInverseSqrtFromProjection K L.starProjection = actualNormalInverseSqrt K L := rfl

section Parameter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Genuine differentiation of the squared projection difference. The two
noncommuting product terms are both retained. -/
theorem fderiv_projectionDefect_right_apply
    (P : V →L[ℝ] V) (R : X → V →L[ℝ] V) (u a : X)
    (hR : DifferentiableAt ℝ R u) :
    fderiv ℝ (fun z ↦ projectionDefect P (R z)) u a =
      -((P - R u) * (fderiv ℝ R u a) + (fderiv ℝ R u a) * (P - R u)) := by
  have hD := (hasFDerivAt_const P u).sub hR.hasFDerivAt
  have hE := hD.clm_comp hD
  change HasFDerivAt (fun z ↦ projectionDefect P (R z)) _ u at hE
  rw [hE.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, zero_apply]
  change (P - R u) * (0 - fderiv ℝ R u a) +
    (0 - fderiv ℝ R u a) * (P - R u) = _
  simp only [zero_sub, mul_neg, neg_mul, neg_add_rev, add_comm]

theorem differentiableAt_projectionDefect_right
    (P : V →L[ℝ] V) (R : X → V →L[ℝ] V) (u : X)
    (hR : DifferentiableAt ℝ R u) :
    DifferentiableAt ℝ (fun z ↦ projectionDefect P (R z)) u := by
  exact ((differentiableAt_const P).sub hR).pow 2

/-- The old-normal inverse square root is differentiable because the actual
projection is differentiable and the fixed analytic series is smooth at the
actual squared defect. -/
theorem differentiableAt_actualNormalInverseSqrtFromProjection
    (K : Submodule ℝ V) (R : X → V →L[ℝ] V) (u : X)
    (hR : DifferentiableAt ℝ R u) (hgap : ‖K.starProjection - R u‖ < 1) :
    DifferentiableAt ℝ (fun z ↦ actualNormalInverseSqrtFromProjection K (R z)) u := by
  have hE := differentiableAt_projectionDefect_right K.starProjection R u hR
  have hS := ((contDiffAt_actualInvSqrt _
    (norm_sub_sq_lt_one K.starProjection (R u) hgap)).differentiableAt (by simp)).comp u hE
  exact (normalProjectionCompressionL K).differentiableAt.comp u hS

/-- The explicit native chain rule for this one constructed H. No derivative
of a chosen inverse square root appears among the assumptions. -/
theorem fderiv_actualNormalInverseSqrtFromProjection_apply
    (K : Submodule ℝ V) (R : X → V →L[ℝ] V) (u a : X)
    (hR : DifferentiableAt ℝ R u) (hgap : ‖K.starProjection - R u‖ < 1) :
    fderiv ℝ (fun z ↦ actualNormalInverseSqrtFromProjection K (R z)) u a =
      normalProjectionCompression K
        (fderiv ℝ actualInvSqrt (projectionDefect K.starProjection (R u))
          (-((K.starProjection - R u) * (fderiv ℝ R u a) +
            (fderiv ℝ R u a) * (K.starProjection - R u)))) := by
  have hE := differentiableAt_projectionDefect_right K.starProjection R u hR
  have hS : DifferentiableAt ℝ actualInvSqrt (projectionDefect K.starProjection (R u)) :=
    (contDiffAt_actualInvSqrt _ (norm_sub_sq_lt_one K.starProjection (R u) hgap)).differentiableAt (by simp)
  have hcomp := hS.hasFDerivAt.comp u hE.hasFDerivAt
  have hH := (normalProjectionCompressionL K).hasFDerivAt.comp u hcomp
  change HasFDerivAt (fun z ↦ actualNormalInverseSqrtFromProjection K (R z)) _ u at hH
  rw [hH.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_projectionDefect_right_apply K.starProjection R u a hR]
  rfl

/-- Joint smoothness of H on the same given projection domain. -/
theorem contDiffOn_actualNormalInverseSqrtFromProjection
    (K : Submodule ℝ V) (R : X → V →L[ℝ] V) (s : Set X)
    (hR : ContDiffOn ℝ ∞ R s) (hgap : ∀ u ∈ s, ‖K.starProjection - R u‖ < 1) :
    ContDiffOn ℝ ∞ (fun z ↦ actualNormalInverseSqrtFromProjection K (R z)) s := by
  intro u hu
  have hE : ContDiffWithinAt ℝ ∞ (fun z ↦ projectionDefect K.starProjection (R z)) s u :=
    (contDiffWithinAt_const.sub (hR u hu)).pow 2
  have hS : ContDiffWithinAt ℝ ∞
      (fun z ↦ actualInvSqrt (projectionDefect K.starProjection (R z))) s u := by
    exact ContDiffAt.comp_contDiffWithinAt
      (f := fun z ↦ projectionDefect K.starProjection (R z)) (g := actualInvSqrt (V := V)) u
      (contDiffAt_actualInvSqrt _ (norm_sub_sq_lt_one K.starProjection (R u) (hgap u hu))) hE
  exact (normalProjectionCompressionL K).contDiff.contDiffAt.comp_contDiffWithinAt u
    hS

/-- The actual family of old-normal inverse square roots is differentiable
under differentiability of its true normal projection family. -/
theorem differentiableAt_actualNormalInverseSqrt
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    DifferentiableAt ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u :=
  differentiableAt_actualNormalInverseSqrtFromProjection K _ u hR hgap

/-- Differentiate the proved identity H²=G.inverse on its actual open
neighborhood, then use the already proved derivative of the native inverse.
This yields the genuine Sylvester identity for the same constructed H. -/
theorem fderiv_actualNormalInverseSqrt_sylvester
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    let H := fun z ↦ actualNormalInverseSqrt K (L z)
    let G := normalProjectionCompression K (L u).starProjection
    (fderiv ℝ H u a) * H u + H u * (fderiv ℝ H u a) =
      -(G.inverse * normalProjectionCompression K
        (fderiv ℝ (fun z ↦ (L z).starProjection) u a) * G.inverse) := by
  intro H G
  let C := fun z ↦ normalProjectionCompression K (L z).starProjection
  have hH : DifferentiableAt ℝ H u := differentiableAt_actualNormalInverseSqrt K L u hR hgap
  have hC : DifferentiableAt ℝ C u := (normalProjectionCompressionL K).differentiableAt.comp u hR
  have hnear : ∀ᶠ z in 𝓝 u, ‖K.starProjection - (L z).starProjection‖ < 1 :=
    ((continuousAt_const.sub hR.continuousAt).norm).eventually (isOpen_Iio.mem_nhds hgap)
  have heq : (fun z ↦ (H z).comp (H z)) =ᶠ[𝓝 u] (fun z ↦ (C z).inverse) := by
    filter_upwards [hnear] with z hz
    exact actualNormalInverseSqrt_sq_eq_inverse K (L z) hz
  have hinv : (C u).IsInvertible :=
    (normalProjectionCompression_inverse_quadratic_bound K (L u)
      ‖K.starProjection - (L u).starProjection‖ hgap le_rfl).1
  have hidentity := congrArg (fun D : X →L[ℝ] K →L[ℝ] K ↦ D a) heq.fderiv_eq
  rw [fderiv_clm_comp hH hH, fderiv_native_inverse_apply C u a hC hinv] at hidentity
  rw [fderiv_normalProjectionCompression_apply K (fun z ↦ (L z).starProjection) u a hR] at hidentity
  exact (add_comm _ _).trans hidentity

/-- The native directional derivative of the same H is self-adjoint. It is
obtained by differentiating H*=H through the actual continuous-linear adjoint. -/
theorem fderiv_actualNormalInverseSqrt_selfAdjoint
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    IsSelfAdjoint (fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a) := by
  let H := fun z ↦ actualNormalInverseSqrt K (L z)
  let adj : (K →L[ℝ] K) →L[ℝ] (K →L[ℝ] K) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := K) (F := K)).toContinuousLinearEquiv.toContinuousLinearMap
  have hH : DifferentiableAt ℝ H u := differentiableAt_actualNormalInverseSqrt K L u hR hgap
  have hadj := adj.hasFDerivAt.comp u hH.hasFDerivAt
  change HasFDerivAt (fun z ↦ adj (H z)) _ u at hadj
  have heq : (fun z ↦ adj (H z)) = H := by
    funext z
    exact (actualNormalInverseSqrt_selfAdjoint K (L z)).adjoint_eq
  have h := congrArg (fun D : X →L[ℝ] K →L[ℝ] K ↦ D a) hadj.fderiv
  change fderiv ℝ (fun z ↦ adj (H z)) u a = adj (fderiv ℝ H u a) at h
  change (fderiv ℝ H u a).adjoint = fderiv ℝ H u a
  rw [heq] at h
  exact h.symm

end Parameter
end GlobalEmbedding.NormalPolar
