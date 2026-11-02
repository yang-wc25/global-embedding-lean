import GlobalEmbedding.Paper.CollarSmoothHolderSlice
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Actual little Hölder membership from a genuine smooth periodic lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-smooth-periodic-membership`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Every genuine smooth integer-periodic lift has a representative in each actual finite-order
little Hölder space for α≤1, without an assumed raw-carrier seed or supplied derivative bounds.

Derive each finite cube jet bound by compactness and a finite actual torus diameter, then
apply W1's published actual smooth-slice constructor. Source: smooth slices in `lem:balanced`. -/
theorem smooth_periodic_little_membership {a N : ℕ} {α : ℝ}
    (g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) (hg : ContDiff ℝ ∞ g)
    (hperiodic : ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      g (x + toLp 2 (fun i ↦ (m i : ℝ))) = g x) (hα : α ≤ 1) (n : ℕ) :
    ∃ f : LittlePeriodicCAlphaFunction a N n α, f.val.toFun = g := by
  have hjet (j : ℕ) : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) → ‖iteratedFDeriv ℝ j g x‖ ≤ C := by
    have hcont : Continuous (fun x : Fin a → ℝ ↦
        iteratedFDeriv ℝ j g (toLp 2 x)) :=
      (hg.continuous_iteratedFDeriv (m := j) (by simp)).comp (PiLp.continuous_toLp _ _)
    have hcompact : IsCompact (Icc (0 : Fin a → ℝ) 1) := isCompact_Icc
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨C, ?_⟩
    intro x hx
    exact hC (ofLp x) ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩
  choose C hC using hjet
  have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
        PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  obtain ⟨g, hg, hnorm⟩ := collar_smooth_holder_slice g hg hperiodic C
    (fun j hj ↦ hC j) hα D (fun x y ↦ hD (mem_univ _) (mem_univ _))
  exact ⟨g, hg⟩


#print axioms smooth_periodic_little_membership

end GlobalEmbedding.Paper
