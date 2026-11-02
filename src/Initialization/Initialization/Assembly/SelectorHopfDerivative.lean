import Initialization.Assembly.SelectorExtension
import GlobalEmbedding.Paper.PlanarHopfGenerator
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The ambient derivative is the actual selector Hopf derivative

The factor velocities include the paper's period-one normalization `2πi`.
The chain rule is applied to the literal sphere orbit and the genuine ambient
extension. No equality between formal and actual derivatives is an input.
-/

noncomputable section
open scoped Manifold ContDiff
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

/-- The actual velocity of the i-th Hopf orbit in the product ambient space. -/
def ambientHopfGenerator {a : ℕ} (C : Fin a → ℕ) (i : Fin a)
    (z : FreeHopfProduct C) : HopfProductAmbient C := fun j ↦
  if j = i then ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
    (z j : PlanarHopfAmbient (C j))) else 0

theorem hopfAmbientOrbit_hasDerivAt {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (z : FreeHopfProduct C) :
    HasDerivAt (fun t : ℝ ↦ hopfProductInclusion C (freeHopfProductFlow C i t z))
      (ambientHopfGenerator C i z) 0 := by
  apply hasDerivAt_pi.2
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [hopfProductInclusion, freeHopfProductFlow_apply,
      ambientHopfGenerator, ite_true] using planarHopfOrbit_hasDerivAt (z i)
  · simpa only [hopfProductInclusion, freeHopfProductFlow_apply_ne C i j hji,
      ambientHopfGenerator, if_neg hji] using
      hasDerivAt_const (0 : ℝ) (z j : PlanarHopfAmbient (C j))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual fderiv of the extension, evaluated at the actual Hopf velocity,
is exactly the already accepted native selector derivative. -/
theorem selectorAmbientExtension_hopf_derivative {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (i : Fin a) (z : FreeHopfProduct C) :
    fderiv ℝ (selectorAmbientExtension C S) (hopfProductInclusion C z)
      (ambientHopfGenerator C i z) = freeHopfDeriv C i S z := by
  have he := (selectorAmbientExtension_contDiffAt C S hS
    (hopfProductInclusion_mem_radial C z)).differentiableAt (by simp)
  have hc := he.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hopfAmbientOrbit_hasDerivAt C i z)
    (by rw [freeHopfProductFlow_zero])
  have hh : (selectorAmbientExtension C S ∘
      (fun t : ℝ ↦ hopfProductInclusion C (freeHopfProductFlow C i t z))) =
      (fun t : ℝ ↦ S (freeHopfProductFlow C i t z)) := by
    funext t
    exact selectorAmbientExtension_inclusion C S _
  rw [hh] at hc
  exact hc.deriv.symm

/-- An arbitrary common real rate vector pushes to the literal ideal derivative
sum used in the colored approximation, at the same sphere argument. -/
theorem selectorAmbientExtension_ideal_velocity {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (S : FreeHopfProduct C → F)
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ S)
    (z : FreeHopfProduct C) (r : Fin a → ℝ) :
    fderiv ℝ (selectorAmbientExtension C S) (hopfProductInclusion C z)
      (∑ i, r i • ambientHopfGenerator C i z) =
      ∑ i, r i • freeHopfDeriv C i S z := by
  simp only [map_sum, map_smul, selectorAmbientExtension_hopf_derivative C S hS]

end GlobalEmbedding.Initialization
