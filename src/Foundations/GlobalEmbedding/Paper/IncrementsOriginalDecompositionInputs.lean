import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Original native positive-decomposition input views

Source: main.tex594–601,638–672. Use the SAME native symmetric bilinear tensor
subtype already in the accepted raw data. Its topology is induced by actual
point evaluation, with no new carrier, norm or chosen basis. The reconstruction
is literally the given finite chi * sqrt(L A) formula and actual d_source phi.
These are qualitative INPUT conditions only: the original quantified uniform
reserve, coordinate-topology equivalence and full admissibility remain explicit
gates before target locking. No mean, solver, bound or result is assumed.
DAG: increments-original-positive-decomposition-input. Exclusive worker W3.
-/

noncomputable section
open Manifold
open scoped BigOperators

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

/-- Native point-evaluation topology on the SAME symmetric fiber already used
in the original raw datum. No topology or norm on all bilinear forms is assumed.
Its equivalence with the original finite-dimensional coordinate topology is an
explicit remaining review/proof gate. Source: original open symmetric fiber. -/
@[instance_reducible]
def incrementsOriginalSymmetricFiberTopology (x : M) :
    TopologicalSpace
      {A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) //
        A.IsSymm} :=
  TopologicalSpace.induced (fun A ↦ fun v w ↦ A.val v w) inferInstance

/-- Literal covector square in the original native bilinear tensor fiber.
Reuse the native bilinear multiplication/pullback; the covector is the actual
source derivative already derived from D.phase. Source: dphi_nu² in594–598. -/
def incrementsOriginalPhaseSquare (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (p : P) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
    (incrementsOriginalPhaseCovector D ν p x).toLinearMap
    (incrementsOriginalPhaseCovector D ν p x).toLinearMap

/-- The original finite positive-decomposition expression on its literal tensor
argument. This is evaluated, not supplied as a desired mean or correction.
Positivity is checked separately, exactly as for native Real.sqrt.
Source: A=sum b_nu(A)² dphi_nu², b_nu=chi_nu sqrt(L_nu A). -/
def incrementsOriginalDecompositionTensor (D : IncrementsOriginalNativeData n d N M P)
    (p : P) (x : M)
    (A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  ∑ ν, (D.cutoff ν (p, x) * Real.sqrt (D.linearArgument ν p x A)) ^ 2 •
    incrementsOriginalPhaseSquare D ν p x

/-- Only the QUALITATIVE original decomposition inputs. The uniform numerical
reserve on required joint supports is deliberately not replaced by this weaker
pointwise positivity field; it is still a missing part of full admissibility.
All identities refer to the SAME actual input fields, never independent matrices
or desired computed iterates. Source: main.tex594–601. -/
structure IncrementsOriginalQualitativeDecompositionInputs
    (D : IncrementsOriginalNativeData n d N M P) : Prop where
  fiber_open : ∀ p ∈ D.parameterOpen, ∀ x,
    @IsOpen _ (incrementsOriginalSymmetricFiberTopology (n := n) x)
      (D.tensorNeighborhood p x)
  H_symmetric : ∀ p ∈ D.parameterOpen, ∀ x, (D.H p x).IsSymm
  reference_symmetric : ∀ p ∈ D.parameterOpen, ∀ x, (D.reference p x).IsSymm
  H_mem : ∀ p (hp : p ∈ D.parameterOpen) x,
    ⟨D.H p x, H_symmetric p hp x⟩ ∈ D.tensorNeighborhood p x
  reference_mem : ∀ p (hp : p ∈ D.parameterOpen) x,
    ⟨D.reference p x, reference_symmetric p hp x⟩ ∈ D.tensorNeighborhood p x
  decomposition : ∀ p ∈ D.parameterOpen, ∀ x A, A ∈ D.tensorNeighborhood p x →
    A.val = incrementsOriginalDecompositionTensor D p x A.val
  argument_positive : ∀ p ∈ D.parameterOpen, ∀ x ν, D.cutoff ν (p, x) ≠ 0 →
    ∀ A ∈ D.tensorNeighborhood p x, 0 < D.linearArgument ν p x A.val

end GlobalEmbedding.Paper
