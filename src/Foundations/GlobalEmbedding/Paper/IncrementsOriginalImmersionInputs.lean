import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates

/-!
# Original actual immersion and coordinate ellipticity inputs

Source: setup:uniform590 and lem:increments594–601. The background is an actual
phase-regular IMMERSION. Canonical GoodCovector does not include immersion.
These original input conditions refer only to the SAME native F and actual
source charts. Ellipticity is in true Euclidean L2 norms, not an auxiliary
Riemannian bundle or a transported norm. No desired Gram/J/correction output
is a field. Existing input prefixes and the original target remain unchanged.
DAG: increments-original-immersion-ellipticity-input. Exclusive worker W3.
-/

noncomputable section
open Manifold

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

/-- Actual ORIGINAL immersion of each background slice on the original parameter
neighborhood, expressed in exactly the native form used by the accepted normal
projection/actual-geometry APIs. Joint smoothness is a separate original input.
It is not inferred from primary GoodCovector or from the presence of a unit normal.
Source: original phase-regular immersion/two-jet input590–601. -/
structure IncrementsOriginalSliceImmersionInputs
    (D : IncrementsOriginalNativeData n d N M P) : Prop where
  immersion : ∀ p ∈ D.parameterOpen, ∀ x : M,
    Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
        (fun y ↦ D.F (p, y)) x)

/-- The ORIGINAL positive coordinate DF ellipticity lower bound. The constant is
fixed structural input, not an independently supplied inverse/Gram estimate.
Upper derivative control remains in the original base2 F profile. Derivatives
here are spatial; all parameter derivatives still enter the original joint norm.
This lower bound alone is not falsely identified with global immersion outside
its stated evaluation domain. Source: original uniform ellipticity590. -/
structure IncrementsOriginalCoordinateEllipticityInputs
    (D : IncrementsOriginalNativeData n d N M P) (c : ℝ) : Prop where
  lower_pos : 0 < c
  lower : ∀ p ∈ D.parameterSet, ∀ i, ∀ y ∈ D.sourceNormDomain i,
    ∀ v : EuclideanSpace ℝ (Fin n),
      c * ‖v‖ ^ 2 ≤
        ‖(fderiv ℝ (fun z ↦ D.F (p, (D.atlas.chart i).symm z)) y) v‖ ^ 2

end GlobalEmbedding.Paper
