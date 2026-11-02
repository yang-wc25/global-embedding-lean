import GlobalEmbedding.Paper.TrueSecondFormFixedFrameSmooth
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness

/-! Actual true-form coefficients for the local legal wave in main.tex1053–1057.
DAG: upgrade-local-true-form-coefficients. The fixed-tensor proof is the existing
internal hsection proof of TrueSecondFormLocalBundleSmooth, specialized to the
actual tangent inverse frame. No quotient norm or tangent metric is introduced. -/

noncomputable section
open Bundle Manifold
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Paper

/-- Extract the accepted fixed-tensor section argument from the actual true-form
bundle proof, using the existing actual product smoothness theorem.
Proof: the old quotient/tensor induction applies unchanged; pure products are the
accepted fixed-frame coefficients and sums use actual linearity. Only the frame
packaging changes from eQ/cS to the original symmetricSquareLinearMap.
Source: defn:phase and the legal projection step of thm:upgrade1053–1057. -/
theorem upgrade_true_form_fixed_tensor_smooth
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) (q : SymmetricSquare E) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z ↦ (trueSecondForm F hF z
        (symmetricSquareLinearMap
          ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap q) :
            EuclideanSpace ℝ (Fin N))) (chartAt H x).source := by
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      have h := true_second_form_fixed_frame_smooth F hF himm x u v
      apply h.congr
      intro z hz
      congr 1
    | add a b ha hb =>
      change ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun z ↦ (trueSecondForm F hF z
          (symmetricSquareLinearMap
            ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap
            (symmetricSquareQuotient E (a + b))) : EuclideanSpace ℝ (Fin N)))
        (chartAt H x).source
      apply (ha.add hb).congr
      intro z hz
      simp only [map_add, symmetricSquareQuotient, Submodule.mkQ_apply,
        Submodule.coe_add, Pi.add_apply]

/-- The actual true second form restricted through any fixed finite coordinate
map has a smooth original ambient CLM coefficient field, with its exact values.
Proof: construct the native CLM from the literal original linear compositions.
Each fixed coordinate evaluation is the extracted fixed tensor j(d), so the
accepted finite-domain manifold operator criterion gives smoothness. No smooth
coefficient, normal frame, or additional norm on the original quotient is assumed.
Source: actual restricted-image projection in original thm:upgrade1053–1057. -/
theorem upgrade_exists_true_form_coefficients
    {E H M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) (j : D →ₗ[ℝ] SymmetricSquare E) :
    ∃ A : M → D →L[ℝ] EuclideanSpace ℝ (Fin N),
      ContMDiffOn I 𝓘(ℝ, D →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞ A
        (chartAt H x).source ∧
      ∀ z d, A z d = (trueSecondForm F hF z
        (symmetricSquareLinearMap
          ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap (j d)) :
            EuclideanSpace ℝ (Fin N)) := by
  let A (z : M) : D →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    LinearMap.toContinuousLinearMap
      ((normalSpace (I := I) F z).subtype.comp ((trueSecondForm F hF z).comp
      ((symmetricSquareLinearMap
        ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap).comp j)))
  refine ⟨A, ?_, fun _ _ ↦ rfl⟩
  intro z hz
  have hAt : ContMDiffAt I 𝓘(ℝ, D →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞ A z := by
    apply (manifold_finite_operator_smooth_iff A z).mpr
    intro d
    exact (upgrade_true_form_fixed_tensor_smooth F hF himm x (j d)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds hz)
  exact hAt.contMDiffWithinAt

#print axioms upgrade_true_form_fixed_tensor_smooth
#print axioms upgrade_exists_true_form_coefficients

end GlobalEmbedding.Paper
