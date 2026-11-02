import GlobalEmbedding.Paper.FrameGramInvertible
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The actual positive compression in the supported-kernel normal variation

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`prop:supported-rank`, lines 1018–1022, equation (9.4).

The compression is the actual orthogonal projection after applying the ambient operator.
The operator need not preserve the subspace. The final specialization constructs its
strict positivity from the actual inverse Gram operator, rather than assuming it.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The literal compression `π_Z G|_Z`, without an invariance assumption on `G`.
Source: `prop:supported-rank`, the positive compression following equation (9.4). -/
def supportedRankPositiveCompression (Z : Submodule ℝ H) (G : H →L[ℝ] H) : Z →L[ℝ] Z :=
  Z.orthogonalProjectionOnto.comp (G.comp Z.subtypeL)

/-- Compression leaves the quadratic value on the subspace unchanged.
Source: `prop:supported-rank`, positivity of the projected inverse-Gram direction. -/
theorem supportedRankPositiveCompression_inner (Z : Submodule ℝ H) (G : H →L[ℝ] H)
    (z : Z) :
    inner ℝ z (supportedRankPositiveCompression Z G z) = inner ℝ (z : H) (G z) := by
  exact Z.inner_orthogonalProjectionOnto_eq_of_mem_left z (G z)

/-- A strictly positive ambient operator has an invertible actual compression.

Proof: its quadratic value is unchanged after compression. A nonzero kernel element
would therefore have a strictly positive zero quadratic value. The resulting injective
endomorphism is surjective in finite dimension and defines a continuous equivalence.
This includes the zero subspace and does not require `G` to preserve `Z`.
Source: `prop:supported-rank`, lines 1020–1022. -/
theorem supportedRank_positive_compression_invertible
    (Z : Submodule ℝ H) (G : H →L[ℝ] H)
    (hG : ∀ v : H, v ≠ 0 → 0 < inner ℝ v (G v)) :
    (∀ z : Z, z ≠ 0 → 0 < inner ℝ z (supportedRankPositiveCompression Z G z)) ∧
      (supportedRankPositiveCompression Z G).IsInvertible := by
  have hpos : ∀ z : Z, z ≠ 0 →
      0 < inner ℝ z (supportedRankPositiveCompression Z G z) := by
    intro z hz
    rw [supportedRankPositiveCompression_inner]
    exact hG z (fun hzero ↦ hz (Subtype.ext hzero))
  refine ⟨hpos, ?_⟩
  let C := supportedRankPositiveCompression Z G
  have hC : Function.Injective C := by
    intro v w h
    have hzero : C (v - w) = 0 := by simp [map_sub, h]
    by_contra hvw
    have hne : v - w ≠ 0 := sub_ne_zero.mpr hvw
    have hp := hpos (v - w) hne
    change 0 < inner ℝ (v - w) (C (v - w)) at hp
    simp only [hzero, inner_zero_right, lt_self_iff_false] at hp
  let e : Z ≃L[ℝ] Z :=
    (LinearEquiv.ofBijective C.toLinearMap
      ⟨hC, LinearMap.injective_iff_surjective.mp hC⟩).toContinuousLinearEquiv
  exact ⟨e, by ext z; rfl⟩

/-- The actual inverse Gram operator is strictly positive.

Proof: write `v=(A* A)w` using the accepted inverse identity. For `v≠0`, also `w≠0`;
symmetry of the real inner product turns the required value into the positive Gram
quadratic value at `w`. No positivity or invariance of the inverse is assumed.
Source: `prop:supported-rank`, `(B*B|_(K⊥))⁻¹` in equation (9.4). -/
theorem supportedRank_inverseGram_strictly_positive
    (A : H →L[ℝ] F) (hA : Function.Injective A) :
    ∀ v : H, v ≠ 0 → 0 < inner ℝ v ((A.adjoint.comp A).inverse v) := by
  let G := A.adjoint.comp A
  have hGram := frame_gram_positive_invertible A hA
  intro v hv
  let w := G.inverse v
  have hw : G w = v := by
    exact congrArg (fun T : H →L[ℝ] H ↦ T v) hGram.2.2.self_comp_inverse
  have hwne : w ≠ 0 := by
    intro hzero
    apply hv
    simpa only [hzero, map_zero] using hw.symm
  have hpos := hGram.2.1 w hwne
  change 0 < inner ℝ v w
  rw [← hw, real_inner_comm]
  exact hpos

/-- The genuine inverse-Gram compression is invertible for every actual subspace.
This is the fixed invertible transform in the normal-direction computation of
`prop:supported-rank`; there is no `G(Z)⊆Z` premise. -/
theorem supportedRank_inverseGram_compression_invertible
    (Z : Submodule ℝ H) (A : H →L[ℝ] F) (hA : Function.Injective A) :
    (∀ z : Z, z ≠ 0 →
      0 < inner ℝ z (supportedRankPositiveCompression Z (A.adjoint.comp A).inverse z)) ∧
      (supportedRankPositiveCompression Z (A.adjoint.comp A).inverse).IsInvertible :=
  supportedRank_positive_compression_invertible Z _
    (supportedRank_inverseGram_strictly_positive A hA)

#print axioms supportedRankPositiveCompression
#print axioms supportedRankPositiveCompression_inner
#print axioms supportedRank_positive_compression_invertible
#print axioms supportedRank_inverseGram_strictly_positive
#print axioms supportedRank_inverseGram_compression_invertible

end GlobalEmbedding.Paper
