import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Periodic extension from an invariant open coefficient domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Source coefficients may be specified only on a complex strip. Extending
by zero outside an integer-translation-invariant open domain preserves their local analytic data.
-/

open Set
open scoped Topology

namespace GlobalEmbedding.Paper

/-- A periodic family on an invariant open domain has an explicit total periodic extension
that agrees on the domain and retains every analytic germ there.

Source: Proposition `prop:collar`, proof lines 530–534, complex strip coefficient domains.
Define the extension to equal g inside the domain and zero outside. Translation invariance
of the domain means an integer shift either leaves both points inside, where g is periodic,
or leaves both outside, where both values are zero. Openness gives a neighborhood of each
domain point on which the extension equals g; equality of germs preserves actual analyticity.
No analyticity at the domain boundary or outside the domain is asserted or required.
-/
theorem collar_periodic_open_extension
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : E → F) (U : Set E) (hU : IsOpen U) (shift : I → E)
    (hinv : ∀ x i, x + shift i ∈ U ↔ x ∈ U)
    (hper : ∀ x ∈ U, ∀ i, g (x + shift i) = g x) :
    ∃ G : E → F,
      (∀ x ∈ U, G x = g x) ∧
      (∀ x i, G (x + shift i) = G x) ∧
      (∀ x ∈ U, AnalyticAt ℂ g x → AnalyticAt ℂ G x) := by
  classical
  let G : E → F := fun x ↦ if x ∈ U then g x else 0
  have heq (x : E) (hx : x ∈ U) : G x = g x := ite_eq_left hx
  refine ⟨G, heq, ?_, ?_⟩
  · intro x i
    by_cases hx : x ∈ U
    · rw [heq _ ((hinv x i).mpr hx), heq x hx]
      exact hper x hx i
    · simp only [G, hx, (hinv x i).not.mpr hx, ite_false]
  · intro x hx hg
    apply hg.congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (heq y hy).symm

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_periodic_open_extension
