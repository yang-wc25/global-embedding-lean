import GlobalEmbedding.Paper.FrameGramInvertible
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual inverses on the kernel complement

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`prop:supported-rank`, lines 1014–1022. The full adjoint has range `(ker B)⊥`;
only the restriction of `B` to that actual subspace is an equivalence.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {S W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The literal restriction of the actual second-form map to its kernel complement.
Source: `prop:supported-rank`, the isomorphism implicit in equation (9.4). -/
def supportedRankKernelComplementMap (B : S →L[ℝ] W) : B.kerᗮ →L[ℝ] W :=
  B.comp B.kerᗮ.subtypeL

omit [FiniteDimensional ℝ W] in
/-- Surjectivity of `B` makes its actual kernel-complement restriction bijective.

Proof: its kernel lies in `ker B ∩ (ker B)⊥=0`. Project any actual preimage to
the kernel complement to obtain a preimage under the restriction. No invariance
of an unrelated subspace is assumed. Source: `prop:supported-rank`, lines 1014–1019. -/
theorem supportedRankKernelComplementMap_bijective (B : S →L[ℝ] W)
    (hB : Function.Surjective B) : Function.Bijective (supportedRankKernelComplementMap B) := by
  constructor
  · intro v w h
    have hker : (v : S) - (w : S) ∈ B.ker := by
      change B ((v : S) - (w : S)) = 0
      change B (v : S) = B (w : S) at h
      simp only [map_sub, h, sub_self]
    have horth : (v : S) - (w : S) ∈ B.kerᗮ := B.kerᗮ.sub_mem v.property w.property
    have hzero : (v : S) - (w : S) = 0 := by
      have hi : (v : S) - (w : S) ∈ B.ker ⊓ B.kerᗮ := ⟨hker, horth⟩
      rw [B.ker.inf_orthogonal_eq_bot] at hi
      exact hi
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · intro y
    obtain ⟨x, hx⟩ := hB y
    let z : B.kerᗮ := ⟨x - B.ker.starProjection x,
      B.ker.sub_starProjection_mem_orthogonal x⟩
    refine ⟨z, ?_⟩
    have hp : B (B.ker.starProjection x) = 0 := (B.ker.orthogonalProjectionOnto x).property
    change B (x - B.ker.starProjection x) = y
    simp only [map_sub, hp, sub_zero, hx]

/-- The genuine continuous equivalence obtained from the actual restricted map.
Source: `prop:supported-rank`, the inverse on `K⊥` in equation (9.4). -/
def supportedRankKernelComplementEquiv (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    B.kerᗮ ≃L[ℝ] W :=
  (LinearEquiv.ofBijective (supportedRankKernelComplementMap B).toLinearMap
    (supportedRankKernelComplementMap_bijective B hB)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ W] in
/-- The equivalence has exactly the original map, restricted to the actual complement.
Source: `prop:supported-rank`, equation (9.4). -/
@[simp] theorem supportedRankKernelComplementEquiv_apply
    (B : S →L[ℝ] W) (hB : Function.Surjective B) (z : B.kerᗮ) :
    supportedRankKernelComplementEquiv B hB z = B z := rfl

/-- The actual full adjoint has range precisely the kernel complement, not all of `S`.
Proof: apply the native finite-dimensional adjoint/range theorem.
Source: `prop:supported-rank`, the actual codomain of `B*`. -/
theorem supportedRank_adjoint_range (B : S →L[ℝ] W) :
    B.adjoint.range = B.kerᗮ := by
  simpa only [ContinuousLinearMap.adjoint_toLinearMap] using
    B.toLinearMap.orthogonal_ker.symm

/-- Every actual adjoint value belongs to the actual kernel complement.
Source: `prop:supported-rank`, `B*ν=e⊙ξ∈K⊥`. -/
theorem supportedRank_adjoint_mem_kernelComplement (B : S →L[ℝ] W) (ν : W) :
    B.adjoint ν ∈ B.kerᗮ := by
  rw [← supportedRank_adjoint_range]
  exact ⟨ν, rfl⟩

/-- The full adjoint becomes an equivalence only after its actual codomain is restricted.

Proof: native adjoint/range duality gives surjectivity onto the complement. If two
adjoint values agree, surjectivity of the original `B` makes their difference orthogonal
to every vector of `W`, hence zero. Source: `prop:supported-rank`, lines 1014–1017. -/
def supportedRankKernelAdjointEquiv (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    W ≃L[ℝ] B.kerᗮ := by
  let f := B.adjoint.codRestrict B.kerᗮ (supportedRank_adjoint_mem_kernelComplement B)
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply ext_inner_left ℝ
      intro y
      obtain ⟨x, rfl⟩ := hB y
      have heq : B.adjoint v = B.adjoint w := congrArg (fun z : B.kerᗮ ↦ (z : S)) h
      simpa only [ContinuousLinearMap.adjoint_inner_right] using congrArg (inner ℝ x) heq
    · intro z
      have hz : (z : S) ∈ B.adjoint.range := by
        rw [supportedRank_adjoint_range]
        exact z.property
      obtain ⟨ν, hν⟩ := hz
      exact ⟨ν, Subtype.ext hν⟩
  exact (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquiv

/-- The restricted adjoint equivalence is the literal full adjoint after inclusion.
Source: `prop:supported-rank`, the precise meaning of the equation defining `νξ`. -/
@[simp] theorem supportedRankKernelAdjointEquiv_apply
    (B : S →L[ℝ] W) (hB : Function.Surjective B) (ν : W) :
    (supportedRankKernelAdjointEquiv B hB ν : S) = B.adjoint ν := rfl

/-- Solving the actual adjoint equation on `K⊥` gives its specified literal right side.
Source: `prop:supported-rank`, `B*νξ=e⊙ξ`. -/
theorem supportedRankKernelAdjointEquiv_symm_spec
    (B : S →L[ℝ] W) (hB : Function.Surjective B) (z : B.kerᗮ) :
    B.adjoint ((supportedRankKernelAdjointEquiv B hB).symm z) = (z : S) := by
  exact congrArg (fun x : B.kerᗮ ↦ (x : S))
    ((supportedRankKernelAdjointEquiv B hB).apply_symm_apply z)

/-- The genuine inverse of the kernel-complement restriction has the actual Gram formula.

Proof: write the input as `Ax`, use the genuine inverse equivalence, and apply the
accepted inverse-Gram identity to `A*Ax`. Source: `prop:supported-rank`, equation (9.4). -/
theorem supportedRankKernelComplementEquiv_symm_gram
    (B : S →L[ℝ] W) (hB : Function.Surjective B) (w : W) :
    (supportedRankKernelComplementEquiv B hB).symm w =
      ((supportedRankKernelComplementMap B).adjoint.comp
        (supportedRankKernelComplementMap B)).inverse
          ((supportedRankKernelComplementMap B).adjoint w) := by
  let A := supportedRankKernelComplementMap B
  let e := supportedRankKernelComplementEquiv B hB
  obtain ⟨x, rfl⟩ := e.surjective w
  have hGram := (frame_gram_positive_invertible A
    (supportedRankKernelComplementMap_bijective B hB).1).2.2
  change e.symm (e x) = (A.adjoint.comp A).inverse (A.adjoint (A x))
  rw [e.symm_apply_apply]
  exact (congrArg (fun T : B.kerᗮ →L[ℝ] B.kerᗮ ↦ T x) hGram.inverse_comp_self).symm

#print axioms supportedRankKernelComplementMap
#print axioms supportedRankKernelComplementMap_bijective
#print axioms supportedRankKernelComplementEquiv
#print axioms supportedRankKernelComplementEquiv_apply
#print axioms supportedRank_adjoint_range
#print axioms supportedRank_adjoint_mem_kernelComplement
#print axioms supportedRankKernelAdjointEquiv
#print axioms supportedRankKernelAdjointEquiv_apply
#print axioms supportedRankKernelAdjointEquiv_symm_spec
#print axioms supportedRankKernelComplementEquiv_symm_gram

end GlobalEmbedding.Paper
