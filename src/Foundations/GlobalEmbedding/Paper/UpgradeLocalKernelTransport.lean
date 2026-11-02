import GlobalEmbedding.Paper.GoodCovector
import GlobalEmbedding.Paper.SaturationEuclideanModel
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Actual kernel transport for the original local legal wave, main.tex1053–1057.
DAG: upgrade-local-kernel-transport. The symmetric-square equivalence and its
subtype law are accepted algebraic providers, with no new tangent norm. -/

noncomputable section
open Bundle Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual chart-linear phase differential identifies the fixed kernel with
the actual phase kernel, and the actual restricted true form is the SAME map
under the accepted algebraic symmetric-square equivalence.

Proof: the actual tangent chart derivative is its native fiber equivalence. The
given exact chain rule, supplied by the local phase theorem, identifies the
mapped fixed kernel with the literal phase kernel. Apply the already accepted
symmetric-square subtype transport identity and the original true form and
ambient normal inclusion. No new quotient functor, coordinate norm, normal frame
or desired image identity is assumed. This internal dictionary's chain-rule
premise is constructed in the full local-wave theorem, not a final hypothesis.
Source: actual phase/free-field transport in original thm:upgrade1053–1057. -/
theorem upgrade_local_kernel_true_form_transport
    {E H M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ} [AddCommGroup D] [Module ℝ D]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (x z : M) (hz : z ∈ (chartAt H x).source)
    (xi : TangentSpace I x →L[ℝ] ℝ) (psi : M → ℝ)
    (hchain : mfderiv I 𝓘(ℝ, ℝ) psi z =
      xi.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x) z))
    (b : D ≃ₗ[ℝ] SymmetricSquare xi.ker) :
    ∃ C : D ≃ₗ[ℝ] SymmetricSquare (mfderiv I 𝓘(ℝ, ℝ) psi z).ker,
      ∀ d, (trueSecondForm F hF z
        (symmetricSquareLinearMap
          ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap
          (symmetricSquareLinearMap xi.ker.subtype (b d))) :
            EuclideanSpace ℝ (Fin N)) =
        (trueSecondForm F hF z
          (symmetricSquareLinearMap (mfderiv I 𝓘(ℝ, ℝ) psi z).ker.subtype (C d)) :
            EuclideanSpace ℝ (Fin N)) := by
  let eta : E →L[ℝ] ℝ := xi
  let K := eta.ker
  let e₀ := trivializationAt E (TangentSpace I) x
  have hz₀ : z ∈ e₀.baseSet := hz
  let e : E ≃ₗ[ℝ] TangentSpace I z := (e₀.linearEquivAt ℝ z hz₀).symm
  have he : e.toLinearMap = (e₀.symmL ℝ z).toLinearMap := by
    ext a
    exact (e₀.symmL_apply hz₀ a).symm
  have hcoord (w : TangentSpace I z) :
      mfderiv I 𝓘(ℝ, ℝ) psi z w = eta (e.symm w) := by
    rw [hchain]
    change eta (mfderiv I 𝓘(ℝ, E) (extChartAt I x) z w) =
      eta ((e₀ ⟨z, w⟩).2)
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hz]
    exact congrArg eta (e₀.continuousLinearMapAt_apply_of_mem ℝ hz₀ w)
  have hK : K.map e.toLinearMap = (mfderiv I 𝓘(ℝ, ℝ) psi z).ker := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      change mfderiv I 𝓘(ℝ, ℝ) psi z (e a) = 0
      rw [hcoord, e.symm_apply_apply]
      exact ha
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      change eta (e.symm w) = 0
      exact (hcoord w).symm.trans hw
  have hsq := saturationSymmetricSquareEquiv_subtype e K
  rw [saturationSymmetricSquareEquiv_toLinearMap e] at hsq
  rw [congrArg symmetricSquareLinearMap he] at hsq
  have hresult : ∃ C : D ≃ₗ[ℝ] SymmetricSquare (K.map e.toLinearMap),
      ∀ d, (trueSecondForm F hF z
        (symmetricSquareLinearMap (e₀.symmL ℝ z).toLinearMap
          (symmetricSquareLinearMap K.subtype (b d))) : EuclideanSpace ℝ (Fin N)) =
        (trueSecondForm F hF z
          (symmetricSquareLinearMap (K.map e.toLinearMap).subtype (C d)) :
            EuclideanSpace ℝ (Fin N)) := by
    refine ⟨b.trans (saturationSymmetricSquareEquiv (e.submoduleMap K)), ?_⟩
    intro d
    exact congrArg (fun q ↦ (trueSecondForm F hF z q : EuclideanSpace ℝ (Fin N)))
      (DFunLike.congr_fun hsq (b d))
  rw [hK] at hresult
  exact hresult

#print axioms upgrade_local_kernel_true_form_transport

end GlobalEmbedding.Paper
