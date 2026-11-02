import GlobalEmbedding.Paper.SaturationOriginalSpace
import GlobalEmbedding.Paper.SaturationSupportedEquality

/-!
# Quadratic saturation and legal value span: FULL original target

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:saturation,
lines947–968 and proof970–995. DAG: `prop-saturation`. Sole worker W5.
The exact full header and theorem proof doc are independently locked by ROOT.
The final proof is assembled below; independent ROOT acceptance remains required.
All definitions in the statement are actual canonical providers with standard axioms.
-/

namespace GlobalEmbedding.Paper

/-- FULL original quadratic saturation and legal value span.

Source: original `prop:saturation`, lines947–968, including its exact dimension
identity (9.3) from the proof. V has only its original finite-dimensional real
normed structure; no extra inner product, model, solver, rank, density, or support
is supplied. The hypothesis d>=1 is precisely the original definition's stated range.
The R carrier is literally the original nonempty FULL-open positive-good-cone set.

Complete natural-language proof:
The actual good/contraction criterion says evaluation on K is injective. Its
actual full-dual locus is open, nonempty by the original phase hypothesis, and
invariant under positive scaling. Encode the actual contractions of a basis of K
and of P by linear polynomials. The actual Gram-adjugate numerator vanishes on
the witnessing cone; polynomial continuation makes it vanish everywhere. At each
good covector its Gram determinant is nonzero, so this gives the same image condition.
Conversely the whole actual good locus witnesses a cone. Thus the original carrier
equals the actual contraction intersection, which proves subspace closure and K<=R.

Use the genuine Euclidean coordinate model of the SAME quotient, preserving actual
evaluation dimensions and support. A maximal evaluation-rank open frame meets the
actual full-rank K locus, because its actual Gram determinant is a nonzero polynomial.
At this good maximal point the evaluation image of R equals that of K, of dimension d.
Hence ALL evaluation ranks are at most d. Apply the accepted full real quadratic-space
dimension bound to get dimR<=d(d+1)/2. No inner product is added to the original V.

The actual contraction kernel is the literal Sym²ker(xi) image. Kernel subtraction
therefore identifies R with the common preimage of the actual restricted B images.
The good index is nonempty, so their intersection lies in rangeB even without ontoB.
Taking orthogonals gives S-perp=B(R). Rank-nullity on R, using K<=R, gives exactly
dimS=dimW-(dimR-d).

If B is onto in the stated target dimension, the accepted ORIGINAL Sym² dimension
formula and rank-nullity give d=n-1>=2. If K is supported on any hyperplane U, its
actual good evaluation image equals U by the sole actual supported-evaluation
provider. Every tensor in the actual Sym²U image therefore belongs to R. The actual
hyperplane inclusion is injective; the sharp bound and its Sym² dimension give
R=Sym²U. The value formula gives dimS=n. At ONE good covector the same K evaluation
is U for every supporting hyperplane, which proves uniqueness among ALL such U.

If no supporting hyperplane exists, suppose dimS<n+1. The exact value formula and
the sharp upper bound force dimR=d(d+1)/2. The actual R operator space has global
maximum evaluation rank d, attained at a good covector. The accepted d>=2 equality
classification gives the FULL supported operator space on a d-plane; its actual
coordinate pullback gives R=Sym²U for an original hyperplane. Then K<=R supports K,
a contradiction. Therefore dimS>=n+1. This proves every original conclusion; d=1
is never used in the equality classification, and n>=3 is required only in the onto
branch. -/
theorem quadratic_saturation_and_legal_value_span
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hPhase : LinearSecondFormPhaseRegular B)
    (hd : 1 ≤ Module.finrank ℝ B.ker) :
    let n := Module.finrank ℝ V
    let K := B.ker
    let d := Module.finrank ℝ K
    let R := originalSaturationSpace B hPhase
    let S := saturationLegalValueSpan B
    Module.finrank ℝ R ≤ d * (d + 1) / 2 ∧
    S.orthogonal = R.map B ∧
    Module.finrank ℝ S = Module.finrank ℝ W - (Module.finrank ℝ R - d) ∧
    (Function.Surjective B → 3 ≤ n → Module.finrank ℝ W = n * (n - 1) / 2 + 1 →
      d = n - 1 ∧
      (∀ U : Submodule ℝ V, Module.finrank ℝ U + 1 = n →
        K ≤ (symmetricSquareLinearMap U.subtype).range →
        R = (symmetricSquareLinearMap U.subtype).range ∧
        Module.finrank ℝ S = n ∧
        ∀ U' : Submodule ℝ V, Module.finrank ℝ U' + 1 = n →
          K ≤ (symmetricSquareLinearMap U'.subtype).range → U' = U) ∧
      ((¬ ∃ U : Submodule ℝ V, Module.finrank ℝ U + 1 = n ∧
          K ≤ (symmetricSquareLinearMap U.subtype).range) →
        n + 1 ≤ Module.finrank ℝ S)) := by
  have _hd : 1 ≤ Module.finrank ℝ B.ker := hd
  dsimp only
  refine ⟨originalSaturationSpace_dimension_bound B hPhase,
    originalSaturationSpace_legalValueSpan_orthogonal B hPhase,
    originalSaturationSpace_legalValueSpan_dimension B hPhase, ?_⟩
  intro honto hn hW
  have hdK := symmetricSquare_surjective_kernel_finrank B honto hW
  refine ⟨hdK, ?_, ?_⟩
  · intro U hU hK
    have hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U := by omega
    refine ⟨originalSaturationSpace_eq_of_supported B hPhase U hU hK hdim,
      originalSaturationSpace_supported_value_dimension B hPhase honto hW U hU hK, ?_⟩
    intro U' hU' hK'
    have hdim' : Module.finrank ℝ B.ker = Module.finrank ℝ U' := by omega
    exact originalSaturationSpace_supported_unique B hPhase U U' hK hK' hdim hdim'
  · intro hns
    exact originalSaturationSpace_nonsupported_value_lower B hPhase honto hn hW hns

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.quadratic_saturation_and_legal_value_span
