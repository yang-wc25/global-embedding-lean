import GlobalEmbedding.Paper.CollarHopfAnalyticCauchyData
import GlobalEmbedding.Paper.FreeInductionDisplacement
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute

/-!
# Pure spatial normal derivative identities on the original initial hypersurface

Source: `main.tex`, Proposition `prop:collar`, lines 539–553.
This specializes the accepted actual-flow normal derivative theorem. Time differentiation,
time/Hopf commutation, the collar PDE and metric propagation belong to W2, outside this file.
-/

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The derivative of the SAME normal is orthogonal to every first column, in every order.

Proof: normal perpendicularity gives the actual first-column equation and the sorted
second-column equation. Existing actual Hopf commutation supplies the reverse-ordered
second equation. Apply the already accepted actual-flow normal derivative theorem to
the literal canonical Hopf flow and the actual first derivative Y_j H. Its existing proof
already differentiates the identically zero real inner product; no product rule is reproved.
Source: the original initial normal constraints in prop:collar539–553. -/
theorem collarHopf_initial_normal_derivative_inner {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H ν : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω ν)
    (hperp : ∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) H x k) = 0) :
    ∀ x i j, inner ℝ (freeHopfDeriv C i ν x) (freeHopfDeriv C j H x) = 0 := by
  have hHs := hH.of_le (by simp : (∞ : ℕ∞ω) ≤ ω)
  have hνs := hν.of_le (by simp : (∞ : ℕ∞ω) ≤ ω)
  have hsecond (x : FreeHopfProduct C) (i j : Fin a) :
      inner ℝ (ν x) (freeHopfDeriv C i (freeHopfDeriv C j H) x) = 0 := by
    obtain hij | hji := le_total i j
    · exact hperp x (Sum.inr ⟨(i, j), hij⟩)
    · rw [freeHopfDeriv_commute_euclidean C H hHs i j]
      exact hperp x (Sum.inr ⟨(j, i), hji⟩)
  intro x i j
  exact free_old_normal_derivative_inner (freeHopfProductSmoothFlow C i)
    ν (freeHopfDeriv C j H) hνs (freeHopfDeriv_contMDiff C H hHs j)
    (fun y ↦ hperp y (Sum.inl j)) (fun y ↦ hsecond y i j) x

/-- Original collar input supplies the SAME analytic Cauchy data and all initial spatial
normal derivative equations. Call the accepted original-data constructor once, retaining
its exact canonical normal and all fields, then specialize the preceding spatial theorem.
No new normal, time equation, CK solution or desired derivative identity is assumed. -/
theorem collarHopf_analytic_cauchy_normal_data (m : ℕ) (hm : 1 ≤ m)
    (C : Fin m → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    ∃ H ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1)),
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1))) ω H ∧
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount m + m + 1))) ω ν ∧
      (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H x) = 1) ∧
      (∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x)) ∧
      (∀ x, ν x = freeOrderedUnitComplement (freeSymmetricColumnCount m + m)
        (fun i ↦ freeFlowColumns (freeHopfProductFlow C) H x
          ((freeCofactorColumnOrder m).symm i))) ∧
      (∀ x, ‖ν x‖ = 1) ∧
      (∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) H x k) = 0) ∧
      (∀ x, LinearIndependent ℝ
        (Sum.elim (fun _ : Unit ↦ ν x) (freeFlowColumns (freeHopfProductFlow C) H x))) ∧
      ∀ x i j, inner ℝ (freeHopfDeriv C i ν x) (freeHopfDeriv C j H x) = 0 := by
  let _ : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
  obtain ⟨H, ν, hH, hν, hmetric, hfree, hνeq, hunit, hperp, hsquare⟩ :=
    collarHopf_analytic_cauchy_data m hm C hC
  exact ⟨H, ν, hH, hν, hmetric, hfree, hνeq, hunit, hperp, hsquare,
    collarHopf_initial_normal_derivative_inner C H ν hH hν hperp⟩

end GlobalEmbedding.Paper
