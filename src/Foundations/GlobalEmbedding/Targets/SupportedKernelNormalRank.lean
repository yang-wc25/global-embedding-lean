import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Paper.SupportedKernelClosedLocus
import GlobalEmbedding.Paper.SupportedRankNormalDirectionCount
import GlobalEmbedding.Paper.SupportedKernelLocalGeometry
import GlobalEmbedding.Paper.SupportedRankLegalVariation
import GlobalEmbedding.Paper.SymmetricSquareNorms
import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The full original supported-kernel locus and its legal normal rank

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 998–1029, in the original onto, phase-regular setting of `prop:saturation`.
Stage 2 full-statement candidate for ROOT review; no acceptance is asserted.
-/

noncomputable section
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance squareRelationsClosed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance squareNormed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- In the original full-rank phase-regular ambient, the literal supported-kernel locus
is relatively closed and has smooth local defining submersions. At every supported
point the actual derivatives of the original legal columns span at least
`q=n(n-1)/2` normal directions. The SAME constructed local equation is used for its
zero-locus, submersion and normal-rank assertions. No local equation, support choice,
global orientation, kernel graph, inverse or rank bound is assumed as an input.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:supported-rank`, lines 998–1029. The original hyperplane is expressed by exact
codimension one in `HasSupportedKernel`; `Eξ` and `ν⊗ξ²` are the literal original
quotient definitions in `SupportedRankLegalVariation`.

Complete proof plan, retaining the full original conclusion:

Put `d=n-1`. At a supported kernel `K⊂Sym²U`, phase regularity gives a good vector
whose contractions map `K` isomorphically to `U`. Thus the common radical is exactly
the line `U⊥` and the support hyperplane is unique. In actual block-kernel charts,
recover that radical by solving the square scalar block at a fixed good vector.
The remaining radical equations define the supported locus exactly and have a
surjective actual differential. Their kernel is the sum of within-`Sym²U` kernel
motions and the `d`-dimensional support-motion family. This constructs the local
defining submersion. Compactness of the unit radical sphere proves relative
closedness in the onto phase-regular ambient, including limits in each kernel chart.

Restrict the actual `B` to `K⊥`, obtaining the proved genuine equivalence `A`.
For each good `ξ=z+te`, solve the actual restricted adjoint equation
`B*ν=e⊙ξ`. The original restriction pairing proves `ν∈Eξ`. The actual block-kernel
derivative of `ν⊗ξ²` is `Q↦-(A*A)⁻¹(e⊙ξ)Q(z,z)`. Its `Z=e⊙V` component is a fixed
invertible transform: the actual compression of the strictly positive inverse Gram
operator to `Z` is strictly positive and invertible, without assuming invariance.

For the strong span bound, use the target-preserving local syzygy argument audited
in `coord/reviews/revised-audit-root-syzygy-alternative.md`. The annihilator of
`span{Q↦Q(z,z)z}` is evaluated at a good nonzero `z0`. Its evaluation image has
dimension at most `d-1`; in its kernel the genuine second derivative of the local
zero identity gives an alternating form descending to `U/ℝz0`. Its dimension is
at most `(d-1)(d-2)/2`, so rank-nullity gives a U-valued span of at least
`d(d+1)/2=q`. Varying `t` supplies the independent `e⊗K*` directions of dimension
`d`: the quadratic evaluation functionals span `K*` on the same open good set.
Thus the actual legal kernel-variation span has at least `q+d` dimensions before
the support-motion quotient. The fixed positive compression preserves its rank;
the actual quotient loses at most `d` dimensions, leaving the required `q`.
Transport this bound through the SAME local defining-submersion differential.
No weaker one-direction result or cubic-monomial counting is substituted.
-/
theorem legal_normal_rank_of_supported_kernels
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1) :
    let ambient : Set (SymmetricSquare V →L[ℝ] W) :=
      {B | Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap}
    let locus : Set (SymmetricSquare V →L[ℝ] W) :=
      {B | HasSupportedKernel B.toLinearMap}
    IsClosed {B : ambient | (B : SymmetricSquare V →L[ℝ] W) ∈ locus} ∧
      ∀ B ∈ ambient, B ∈ locus →
        ∃ chart : SupportedLocusLocalEquations ambient locus B,
          Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 ≤
            Module.finrank ℝ (Submodule.span ℝ
              {v : Fin chart.codim → ℝ |
                ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
                  ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
                    v = (fderiv ℝ chart.equation B)
                      (supportedRankLegalVariation ξ ν).toContinuousLinearMap}) := by
  dsimp only
  constructor
  · exact isClosed_supportedKernel_surjective_phaseRegular
  · intro B hB hlocus
    obtain ⟨U, hU, hK⟩ := hlocus
    obtain ⟨e, he, he0, chart, M, hf, hk⟩ :=
      exists_supportedKernelLocalEquations_original B hB.1 hB.2 hn hW U hU hK
    refine ⟨chart, ?_⟩
    exact supportedRank_actual_equation_legal_span_finrank B hB.1 hB.2 hn hW U hU hK
      e he he0 chart.equation M hf hk

#print axioms legal_normal_rank_of_supported_kernels
#print axioms squareRelationsClosed
#print axioms squareNormed

end GlobalEmbedding.Paper
