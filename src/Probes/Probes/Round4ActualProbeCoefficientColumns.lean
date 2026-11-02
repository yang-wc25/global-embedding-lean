import Probes.Round4ActualProbeMeanHessian
import Probes.ActualIncrementPrimaryCoefficientBinding

/-!
# Actual differentiated coefficients retain finite parameter columns

These identities distribute the actual spatial derivative only after checking
the genuine amplitude-column differentiability. The cutoff derivatives,
phase derivatives, both real/imaginary channels and their signs are retained.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {ι A : Type*} [Fintype ι] [Fintype A] {n N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem round4_primary_coefficient_sum
    (phi : D → ℝ) (tau : ℝ) (chi : A → D → ℝ)
    (P Q : ι → A → D → V) (x v : D)
    (hP : ∀ q a, DifferentiableAt ℝ (P q a) x)
    (hQ : ∀ q a, DifferentiableAt ℝ (Q q a) x) :
    incrementsPrimaryDerivativeCoefficient phi tau chi
      (fun a y => ∑ q, P q a y) (fun a y => ∑ q, Q q a y) x v =
        ∑ q, incrementsPrimaryDerivativeCoefficient phi tau chi (P q) (Q q) x v := by
  have hdP (a : A) : fderiv ℝ (fun y => ∑ q, P q a y) x =
      ∑ q, fderiv ℝ (P q a) x := fderiv_fun_sum (fun q _ => hP q a)
  have hdQ (a : A) : fderiv ℝ (fun y => ∑ q, Q q a y) x =
      ∑ q, fderiv ℝ (Q q a) x := fderiv_fun_sum (fun q _ => hQ q a)
  ext c
  simp only [incrementsPrimaryDerivativeCoefficient,Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [hdP,hdQ]
  simp only [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,Complex.ofReal_sum,
    Finset.mul_sum,← Finset.sum_add_distrib]

theorem round4_primary_coefficient_finite_source
    (phi : D → ℝ) (tau : ℝ) (chi : A → D → ℝ)
    (P Q : ι → A → D → V) (x v : D)
    (hP : ∀ q a, DifferentiableAt ℝ (P q a) x)
    (hQ : ∀ q a, DifferentiableAt ℝ (Q q a) x) (u : ι → ℝ) :
    incrementsPrimaryDerivativeCoefficient phi tau chi
      (fun a => finiteProbeSource (fun q => P q a) u)
      (fun a => finiteProbeSource (fun q => Q q a) u) x v =
        ∑ q, u q • incrementsPrimaryDerivativeCoefficient phi tau chi (P q) (Q q) x v := by
  change incrementsPrimaryDerivativeCoefficient phi tau chi
    (fun a y => ∑ q, u q • P q a y) (fun a y => ∑ q, u q • Q q a y) x v = _
  rw [round4_primary_coefficient_sum phi tau chi
    (fun q a y => u q • P q a y) (fun q a y => u q • Q q a y) x v
    (fun q a => (hP q a).const_smul (u q)) (fun q a => (hQ q a).const_smul (u q))]
  apply Finset.sum_congr rfl
  intro q _
  exact actual_primary_derivative_coefficient_smul phi tau (u q) chi (P q) (Q q) x v

/-- Actual amplitude germs supply the exact native coefficient map. -/
theorem round4_primary_coefficient_germ_columns
    (phi : D → ℝ) (tau : ℝ) (chi : A → D → ℝ)
    (P Q : ι → A → D → V) (R S : A → D → V) (x v : D)
    (hP : ∀ q a, DifferentiableAt ℝ (P q a) x)
    (hQ : ∀ q a, DifferentiableAt ℝ (Q q a) x) (u : ι → ℝ)
    (hR : ∀ a, R a =ᶠ[𝓝 x] finiteProbeSource (fun q => P q a) u)
    (hS : ∀ a, S a =ᶠ[𝓝 x] finiteProbeSource (fun q => Q q a) u) :
    incrementsPrimaryDerivativeCoefficient phi tau chi R S x v =
      ∑ q, u q • incrementsPrimaryDerivativeCoefficient phi tau chi (P q) (Q q) x v := by
  rw [primaryDerivativeCoefficient_congr_germs phi tau chi R S _ _ x v hR hS]
  exact round4_primary_coefficient_finite_source phi tau chi P Q x v hP hQ u

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4_primary_coefficient_sum
#print axioms GlobalEmbedding.Continuation.round4_primary_coefficient_finite_source
#print axioms GlobalEmbedding.Continuation.round4_primary_coefficient_germ_columns
