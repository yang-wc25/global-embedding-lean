import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual period-one orbit calculus for the planar selectors

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`,
lines 245–266. The derivative is the actual one-variable derivative of the orbit map;
the average integrates over the original period one. Raw curried flows are accepted so
the Fourier, reparametrization and native Hopf constructions share the same operations.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The planar selector has the actual Euclidean, rather than supremum, norm. -/
abbrev Planar := EuclideanSpace ℝ (Fin 2)

/-- The free space curve has the actual Euclidean norm in dimension three. -/
abbrev SpaceCurve := EuclideanSpace ℝ (Fin 3)

/-- The reflection appearing in the original antipodal identity. -/
def planarReflection (v : Planar) : Planar := WithLp.toLp 2 ![v 0, -v 1]

/-- The positively oriented quarter turn used to define signed curvature. -/
def planarQuarterTurn (v : Planar) : Planar := WithLp.toLp 2 ![-v 1, v 0]

/-- Differentiation along the actual orbit, with time measured in periods of length one. -/
def orbitDeriv {M F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → M → M) (f : M → F) (x : M) : F :=
  deriv (fun t : ℝ ↦ f (R t x)) 0

/-- The actual interval integral over a single period. -/
def orbitAverage {M F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → M → M) (f : M → F) (x : M) : F :=
  ∫ t in (0 : ℝ)..1, f (R t x)

/-- Actual smooth flow data. These fields contain no proposed selector, inverse or derivative. -/
structure PeriodOneSmoothFlow {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  flow : ℝ → M → M
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)
  flow_one : ∀ x, flow 1 x = x
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ flow p.1 p.2)

/-- Translating the starting point gives the same actual derivative at the translated time.
This is the ordinary translation rule for `deriv`, applied to the genuine flow law. -/
theorem orbitDeriv_flow {M F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → F) (t : ℝ) (x : M) :
    orbitDeriv R f (R t x) = deriv (fun s : ℝ ↦ f (R s x)) t := by
  unfold orbitDeriv
  simp_rw [← hR]
  simpa using (deriv_comp_add_const (f := fun s : ℝ ↦ f (R s x)) t 0)

/-- Every orbit observable has period one, directly from the genuine action laws. -/
theorem orbitMap_periodic {M F : Type*} (R : ℝ → M → M)
    (hR : ∀ s t x, R (s + t) x = R s (R t x)) (h1 : ∀ x, R 1 x = x)
    (f : M → F) (x : M) : Function.Periodic (fun t ↦ f (R t x)) 1 := by
  intro t
  change f (R (t + 1) x) = f (R t x)
  rw [hR, h1]

@[simp] theorem planarReflection_apply_zero (v : Planar) : planarReflection v 0 = v 0 := rfl
@[simp] theorem planarReflection_apply_one (v : Planar) : planarReflection v 1 = -v 1 := rfl

@[simp] theorem planarQuarterTurn_apply_zero (v : Planar) :
    planarQuarterTurn v 0 = -v 1 := rfl
@[simp] theorem planarQuarterTurn_apply_one (v : Planar) :
    planarQuarterTurn v 1 = v 0 := rfl

#print axioms orbitDeriv_flow
#print axioms orbitMap_periodic

end GlobalEmbedding.Paper
