import GlobalEmbedding.Paper.FrameGramInverseIdentities
import GlobalEmbedding.Paper.SmoothFrameGramCoefficients
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Real selfadjoint spaces of bounded evaluation rank

Source: revised manuscript `parallelizable-stable-revised-2026-10-30.tex`,
lines 1779–1843, independently audited in `coord/reviews/revised-audit-W1.md`.
These are actual continuous endomorphisms of a real Euclidean space. The original
binary symmetric quotient is not replaced; W2 provides its separate dictionary.
-/

noncomputable section
open scoped Topology
open Module

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Actual evaluation, restricted to the operator subspace. -/
def quadraticSpaceEvaluation (P : Submodule ℝ (V →L[ℝ] V)) (x : V) : P →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V x).comp P.subtypeL

@[simp] theorem quadraticSpaceEvaluation_apply
    (P : Submodule ℝ (V →L[ℝ] V)) (x : V) (Q : P) :
    quadraticSpaceEvaluation P x Q = (Q : V →L[ℝ] V) x := rfl

/-- If every evaluation image is zero, the operator space itself is zero.
This includes the zero-dimensional ambient space and handles the d=0 boundary. -/
theorem quadraticSpace_eq_bot_of_evaluation_zero
    (P : Submodule ℝ (V →L[ℝ] V))
    (h : ∀ x, LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap = ⊥) :
    P = ⊥ := by
  apply le_antisymm _ bot_le
  intro Q hQ
  suffices Q = 0 by simp [this]
  ext x
  have hx : Q x ∈ LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap :=
    ⟨⟨Q, hQ⟩, rfl⟩
  simpa [h x] using hx

/-- A local differentiable column representation forces every evaluation-kernel
operator to take values in the fixed column space at the base point.

Proof: differentiating the genuine local identity Qx=A(x)c(x), with c(x0)=0,
leaves only A(x0) Dc(x0). This is an internal calculus lemma; no local coefficients
are assumed in the final dimension statement. Actual coefficients are the accepted
Gram inverse, with local injectivity supplied by maximum evaluation rank.
Source: revised proof lines1800–1809. -/
theorem quadraticSpace_kernel_range_of_local_coefficients
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : V → D →L[ℝ] V) (c : V → D) (Q : V →L[ℝ] V) (x₀ : V)
    (A' : V →L[ℝ] D →L[ℝ] V) (c' : V →L[ℝ] D)
    (hA : HasFDerivAt A A' x₀) (hc : HasFDerivAt c c' x₀)
    (hzero : c x₀ = 0) (heq : (fun x ↦ A x (c x)) =ᶠ[𝓝 x₀] Q) :
    LinearMap.range Q.toLinearMap ≤ LinearMap.range (A x₀).toLinearMap := by
  have hd := (hA.clm_apply hc).congr_of_eventuallyEq heq.symm
  have hder : (A x₀).comp c' + A'.flip (c x₀) = Q :=
    hd.unique Q.hasFDerivAt
  rw [hzero] at hder
  simp only [map_zero, add_zero] at hder
  rintro _ ⟨v, rfl⟩
  exact ⟨c' v, congrArg (fun T : V →L[ℝ] V ↦ T v) hder⟩

/-- Symmetry makes a map killed at x0 take values perpendicular to x0. -/
theorem quadraticSpace_kernel_inner_zero
    (Q : V →L[ℝ] V) (hQ : Q.toLinearMap.IsSymmetric) {x₀ : V}
    (hx : Q x₀ = 0) (v : V) : inner ℝ (Q v) x₀ = 0 := by
  calc
    inner ℝ (Q v) x₀ = inner ℝ v (Q x₀) := hQ v x₀
    _ = 0 := by rw [hx, inner_zero_right]

/-- The actual kernel range lies in E=U0 intersect x0-perp; no compression has
been silently identified with the original operator.
Source: revised lines1807–1810. -/
theorem quadraticSpace_kernel_range_supported
    (Q : V →L[ℝ] V) (hQ : Q.toLinearMap.IsSymmetric) {x₀ : V}
    (hx : Q x₀ = 0) (U : Submodule ℝ V)
    (hr : LinearMap.range Q.toLinearMap ≤ U) :
    ∀ v, Q v ∈ U ⊓ (ℝ ∙ x₀)ᗮ := by
  intro v
  refine ⟨hr ⟨v, rfl⟩, ?_⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    (quadraticSpace_kernel_inner_zero Q hQ hx v)

/-- Range containment of a selfadjoint operator also forces it to kill the
orthogonal complement; this is the literal support assertion used in equality.
Source: revised lines1810,1841–1842. -/
theorem quadraticSpace_kills_orthogonal
    (Q : V →L[ℝ] V) (hQ : Q.toLinearMap.IsSymmetric)
    (U : Submodule ℝ V) (hr : LinearMap.range Q.toLinearMap ≤ U)
    {v : V} (hv : v ∈ Uᗮ) : Q v = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ (Q v) (Q v) = inner ℝ v (Q (Q v)) := hQ v (Q v)
    _ = 0 := (U.mem_orthogonal' v).mp hv (Q (Q v)) (hr ⟨Q v, rfl⟩)

#print axioms quadraticSpace_eq_bot_of_evaluation_zero
#print axioms quadraticSpace_kernel_range_of_local_coefficients
#print axioms quadraticSpace_kernel_range_supported
#print axioms quadraticSpace_kills_orthogonal

end GlobalEmbedding.Paper
