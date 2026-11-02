import Initialization.Phase.SelectorSecondError

/-!
# Quantitative bounds for the actual selector second-jet remainder

The derivative bounds for the genuine Hopf columns are produced on the whole
compact sphere product from the fixed selector. The number of patches never
occurs. The final quotient budget is in the original canonical symmetric-square
norm and retains the original fixed actual-Hessian-lift constant.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance secondBoundRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance secondBoundSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {n N : ℕ} (C : Fin n → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))

/-- The fixed selector internally supplies one bound on every actual derivative
of its Hopf columns, over its entire native domain and before K,T. -/
theorem selectorHopfExtension_uniform_first_bound
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ i z,
      ‖fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
        (hopfProductInclusion C z)‖ ≤ B := by
  have hs (i : Fin n) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C i S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C i)
      (freeHopfProductFlow_contMDiff C i) S hS
  have each (i : Fin n) := selectorAmbientExtension_uniform_derivatives C
    (freeHopfDeriv C i S) (hs i)
  choose b hb hbderiv using each
  refine ⟨1 + ∑ i, b i 1, ?_, ?_⟩
  · have h : 0 ≤ ∑ i, b i 1 := Finset.sum_nonneg (fun i _ ↦ (hb i 1).le)
    linarith
  · intro i z
    have h : ‖fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
        (hopfProductInclusion C z)‖ ≤ b i 1 := by
      simpa only [norm_iteratedFDeriv_one] using hbderiv i 1 z
    have hi : b i 1 ≤ ∑ i, b i 1 :=
      Finset.single_le_sum (fun i _ ↦ (hb i 1).le) (Finset.mem_univ i)
    exact h.trans (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The true second-derivative remainder is bounded by the actual ambient
first error and the derivative of the actual selected-map first error. -/
theorem selectorSourceSecondError_norm_le
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) {x : E}
    (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hc : ContDiffAt ℝ ∞ c x)
    (B : ℝ) (hB : 0 ≤ B)
    (hcolumn : ∀ i, ‖fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
      (selectorSourceAmbient C z x)‖ ≤ B) :
    ‖selectorSourceSecondError C S z c x‖ ≤
      (n : ℝ) * ‖c x‖ * B * ‖selectorSourceAmbientError C z (selectorCoframeRates c) x‖ +
      ‖fderiv ℝ (selectorSourceFirstError C S z (selectorCoframeRates c)) x‖ := by
  let ambientError := selectorSourceAmbientError C z (selectorCoframeRates c) x
  let firstErrorDerivative := fderiv ℝ (selectorSourceFirstError C S z (selectorCoframeRates c)) x
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  have hcoeff (i : Fin n) : ‖c x w i‖ ≤ ‖c x‖ * ‖w‖ :=
    (PiLp.norm_apply_le (c x w) i).trans ((c x).le_opNorm w)
  have hcol (i : Fin n) :
      ‖fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
        (selectorSourceAmbient C z x) (ambientError v)‖ ≤
      B * (‖ambientError‖ * ‖v‖) :=
    (fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
      (selectorSourceAmbient C z x)).le_of_opNorm_le_of_le (hcolumn i)
        (ambientError.le_opNorm v)
  rw [selectorSourceSecondError_apply C S hS z c hz hc]
  calc
    _ ≤ (∑ i, ‖c x w i •
        fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
          (selectorSourceAmbient C z x) (ambientError v)‖) +
        ‖firstErrorDerivative v w‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ _i : Fin n, (‖c x‖ * ‖w‖) * (B * (‖ambientError‖ * ‖v‖))) +
        ‖firstErrorDerivative‖ * ‖v‖ * ‖w‖ := by
      apply add_le_add _ (firstErrorDerivative.le_opNorm₂ v w)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (hcoeff i) (hcol i) (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The fixed canonical lift converts the genuine bilinear error to the entire
second-jet operator budget used by the original phase-stability theorem. -/
theorem coordinateHessianJet_selector_error_bound
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) {x : E}
    (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hc : ContDiffAt ℝ ∞ c x)
    (B : ℝ) (hB : 0 ≤ B)
    (hcolumn : ∀ i, ‖fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
      (selectorSourceAmbient C z x)‖ ≤ B) :
    ‖coordinateHessianJet (S ∘ z) x -
      ((selectorIdealSecondJet C S (z x)).comp (symmetricSquareMapL (c x)) +
        (selectorIdealFirstJet C S (z x)).comp (actualHessianLift (fderiv ℝ c x)))‖ ≤
      actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ((n : ℝ) * ‖c x‖ * B * ‖selectorSourceAmbientError C z (selectorCoframeRates c) x‖ +
          ‖fderiv ℝ (selectorSourceFirstError C S z (selectorCoframeRates c)) x‖) :=
  (coordinateHessianJet_selector_error_norm_le C S z c x).trans
    (mul_le_mul_of_nonneg_left
      (selectorSourceSecondError_norm_le C S hS z c hz hc B hB hcolumn)
      actualHessianLiftConstant_nonneg)

end GlobalEmbedding.Initialization
