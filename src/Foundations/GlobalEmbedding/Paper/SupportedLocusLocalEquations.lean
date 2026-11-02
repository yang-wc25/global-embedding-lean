import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!+# Literal supported kernels and their actual local defining equations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 998–1006. The kernel and inclusion below are the original binary symmetric-square maps.
The local-equation structure records actual data to be constructed in the conclusion of the
geometry theorem. It does not assume the supported locus is already a manifold.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The literal original supported-kernel condition with exact hyperplane codimension one.
Source: `prop:supported-rank`, inherited equation (9.2). No auxiliary norm is introduced. -/
def HasSupportedKernel (B : SymmetricSquare V →ₗ[ℝ] W) : Prop :=
  ∃ U : Submodule ℝ V, Module.finrank ℝ U + 1 = Module.finrank ℝ V ∧
    B.ker ≤ (symmetricSquareLinearMap U.subtype).range

/-- A nonzero covector is good for the actual linear second form when its original literal
symmetric-square kernel restriction is injective. Source: `defn:phase`, used in
`prop:supported-rank`. This is independent of the later normed realization. -/
def LinearSecondFormGoodCovector (B : SymmetricSquare V →ₗ[ℝ] W)
    (ξ : V →ₗ[ℝ] ℝ) : Prop :=
  ξ ≠ 0 ∧ Function.Injective (B.comp (symmetricSquareLinearMap ξ.ker.subtype))

/-- The original phase-regular condition on an actual linear second form.
Source: `defn:phase` and the ambient of `prop:supported-rank`. -/
def LinearSecondFormPhaseRegular (B : SymmetricSquare V →ₗ[ℝ] W) : Prop :=
  ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B ξ

/-- Actual smooth local defining-submersion data on an open ambient. The zero set agrees
with the specified original subset on the whole neighborhood, and the actual differential
is surjective at the specified point. Source: `prop:supported-rank`, smooth embedded locus;
this is the local-equation formulation consumed by `finite_parameter_avoidance_submanifold`.
The geometry theorem must construct these data; they are never an original input hypothesis. -/
structure SupportedLocusLocalEquations
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ambient locus : Set X) (x : X) where
  /-- Dimension of the actual finite normal-equation target. -/
  codim : ℕ
  /-- Actual ambient neighborhood of the specified point. -/
  domain : Set X
  /-- Actual defining map, represented by a total function smooth on its domain. -/
  equation : X → Fin codim → ℝ
  /-- The defining neighborhood is open. -/
  isOpen_domain : IsOpen domain
  /-- It contains the specified point. -/
  mem_domain : x ∈ domain
  /-- All local equations stay within the original ambient open set. -/
  domain_subset : domain ⊆ ambient
  /-- Genuine infinite smoothness of the defining function on its neighborhood. -/
  contDiffOn_equation : ContDiffOn ℝ ∞ equation domain
  /-- Exact zero-locus equivalence with the original specified subset. -/
  mem_locus_iff : ∀ y ∈ domain, y ∈ locus ↔ equation y = 0
  /-- Surjectivity of the actual derivative, not a supplied formal normal-space map. -/
  surjective_fderiv : Function.Surjective (fderiv ℝ equation x)

end GlobalEmbedding.Paper
