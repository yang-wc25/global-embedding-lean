import Probes.ActualMeanParity
import Probes.ActualReconstructedParameter

/-!
# Actual primary-wave amplitudes supply zero-phase mean parity

This bridges native real/imaginary amplitudes and the original differentiated
complex coefficient. Reflection is proved from equality of the actual amplitude
germs; it is not postulated for a formal derivative carrier. Actual supports and
the genuine phase-germ separation then supply evenness of the complete mean.
The homogeneous correction's odd germs are supplied by
`primaryReconstructedParameter_neg` on the original open chart.
-/

noncomputable section
open GlobalEmbedding.Paper Filter Set
open scoped Topology ContDiff BigOperators

namespace GlobalEmbedding.Continuation

/-- The original differentiated coefficient depends on actual amplitude germs. -/
theorem primaryDerivativeCoefficient_congr_germs {A : Type*} [Fintype A] {n N : ℕ}
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q P' Q' : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n))
    (hP : ∀ a, P a =ᶠ[𝓝 x] P' a) (hQ : ∀ a, Q a =ᶠ[𝓝 x] Q' a) :
    incrementsPrimaryDerivativeCoefficient phi tau chi P Q x v =
      incrementsPrimaryDerivativeCoefficient phi tau chi P' Q' x v := by
  funext c
  unfold incrementsPrimaryDerivativeCoefficient
  apply Finset.sum_congr rfl
  intro a _
  rw [(hP a).eq_of_nhds, (hQ a).eq_of_nhds, (hP a).fderiv_eq, (hQ a).fderiv_eq]

/-- Negating both actual amplitudes negates every differentiated coefficient,
including cutoff derivatives and the phase term. -/
theorem primaryDerivativeCoefficient_neg {A : Type*} [Fintype A] {n N : ℕ}
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) :
    incrementsPrimaryDerivativeCoefficient phi tau chi
      (fun a y => -P a y) (fun a y => -Q a y) x v =
        -incrementsPrimaryDerivativeCoefficient phi tau chi P Q x v := by
  funext c
  simp only [incrementsPrimaryDerivativeCoefficient, Pi.neg_apply, fderiv_fun_neg,
    neg_apply, WithLp.ofLp_neg, Complex.ofReal_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Actual original differentiated coefficients for a parameterized amplitude
family. The directions may be the original coordinate vectors or arbitrary ones. -/
def actualPrimaryCoefficientFamily {Λ A J P : Type*} [Fintype A] {n N : ℕ}
    (phi : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (ReAmp ImAmp : P → Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin n)) (v : J → EuclideanSpace ℝ (Fin n))
    (u : P) (l : Λ) (j : J) : Fin N → ℂ :=
  incrementsPrimaryDerivativeCoefficient (phi l) tau (chi l) (ReAmp u l) (ImAmp u l) x (v j)

/-- The exact coefficient reflection follows from the actual source amplitude
reflection on each original local germ. -/
theorem actualPrimaryCoefficientFamily_reflect {Λ A J P : Type*} [Fintype A]
    [Neg P] {n N : ℕ} (probe : Λ → Bool)
    (phi : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (ReAmp ImAmp : P → Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin n)) (v : J → EuclideanSpace ℝ (Fin n)) (u : P)
    (hRe : ∀ l a, ReAmp (-u) l a =ᶠ[𝓝 x]
      if probe l then -ReAmp u l a else ReAmp u l a)
    (hIm : ∀ l a, ImAmp (-u) l a =ᶠ[𝓝 x]
      if probe l then -ImAmp u l a else ImAmp u l a) :
    actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v (-u) =
      reflectProbeCoefficients probe (actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v u) := by
  funext l j
  change incrementsPrimaryDerivativeCoefficient _ _ _ _ _ _ _ = _
  rw [primaryDerivativeCoefficient_congr_germs (phi l) tau (chi l)
    (ReAmp (-u) l) (ImAmp (-u) l)
    (fun a => if probe l then -ReAmp u l a else ReAmp u l a)
    (fun a => if probe l then -ImAmp u l a else ImAmp u l a)
    x (v j) (hRe l) (hIm l)]
  cases hp : probe l
  · simp [hp, reflectProbeCoefficients, actualPrimaryCoefficientFamily]
  · have hReFun : (fun a => -ReAmp u l a) = (fun a y => -ReAmp u l a y) := by
      funext a y
      rfl
    have hImFun : (fun a => -ImAmp u l a) = (fun a y => -ImAmp u l a y) := by
      funext a y
      rfl
    simpa [hp, reflectProbeCoefficients, actualPrimaryCoefficientFamily, hReFun, hImFun] using
      primaryDerivativeCoefficient_neg (phi l) tau (chi l) (ReAmp u l) (ImAmp u l) x (v j)

/-- Actual amplitude support supplies support of the actual coefficient family. -/
theorem actualPrimaryCoefficientFamily_support {Λ A J P : Type*} [Fintype A] {n N : ℕ}
    (phi : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (ReAmp ImAmp : P → Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (S : Λ → Set (EuclideanSpace ℝ (Fin n)))
    (hRe : ∀ u l a, tsupport (ReAmp u l a) ⊆ S l)
    (hIm : ∀ u l a, tsupport (ImAmp u l a) ⊆ S l)
    (x : EuclideanSpace ℝ (Fin n)) (v : J → EuclideanSpace ℝ (Fin n)) :
    ∀ u l, x ∉ S l → ∀ j, actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v u l j = 0 := by
  intro u l hx j
  exact increments_primary_coefficient_of_notMem_support (phi l) tau (chi l)
    (ReAmp u l) (ImAmp u l) (S l) (hRe u l) (hIm u l) x (v j) hx

/-- Evenness of the actual zero-phase germ coefficient of the actual primary
wave. No coefficient reflection or coefficient support is assumed separately. -/
theorem actual_primary_zero_mean_even {Λ A J P : Type*} [Fintype Λ] [Fintype A]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {n N : ℕ} (probe : Λ → Bool)
    (phi : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (chi : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (ReAmp ImAmp : P → Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (S : Λ → Set (EuclideanSpace ℝ (Fin n)))
    (hReSupp : ∀ u l a, tsupport (ReAmp u l a) ⊆ S l)
    (hImSupp : ∀ u l a, tsupport (ImAmp u l a) ⊆ S l)
    (x : EuclideanSpace ℝ (Fin n)) (v : J → EuclideanSpace ℝ (Fin n))
    (hRe : ∀ u l a, ReAmp (-u) l a =ᶠ[𝓝 x]
      if probe l then -ReAmp u l a else ReAmp u l a)
    (hIm : ∀ u l a, ImAmp (-u) l a =ᶠ[𝓝 x]
      if probe l then -ImAmp u l a else ImAmp u l a)
    (hdouble : ∀ l, x ∈ S l → fderiv ℝ (fun y => phi l y / tau + phi l y / tau) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → x ∈ S l → x ∈ S k →
      fderiv ℝ (fun y => phi l y / tau + phi k y / tau) x ≠ 0 ∧
        fderiv ℝ (fun y => phi l y / tau - phi k y / tau) x ≠ 0)
    (i j : J) (u : P) :
    actualParameterZeroMean (fun l y => phi l y / tau)
      (actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v) x i j (-u) =
    actualParameterZeroMean (fun l y => phi l y / tau)
      (actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v) x i j u := by
  exact actualParameterZeroMean_even probe (fun l y => phi l y / tau)
    (actualPrimaryCoefficientFamily phi tau chi ReAmp ImAmp x v) S x
    (fun w => actualPrimaryCoefficientFamily_reflect probe phi tau chi ReAmp ImAmp x v w (hRe w) (hIm w))
    (actualPrimaryCoefficientFamily_support phi tau chi ReAmp ImAmp S hReSupp hImSupp x v)
    hdouble hinteraction i j u

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.primaryDerivativeCoefficient_neg
#print axioms GlobalEmbedding.Continuation.actualPrimaryCoefficientFamily_reflect
#print axioms GlobalEmbedding.Continuation.actual_primary_zero_mean_even
