import GlobalEmbedding.Paper.CollarSmoothHolderSlice
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Genuine smooth periodic lifts belong to every actual finite little Hölder order

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-smooth-upgrade`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Every actual smooth periodic lift has an actual little Hölder representative at every
finite spatial order, with exactly the same underlying function, for α≤1.

Proof: continuity bounds each finite jet on the compact coordinate cube. The actual flat
torus is compact and hence has finite diameter. Apply the published actual smooth periodic
slice constructor with those concrete bounds. No upgraded carrier membership is assumed.
Source: smooth periodic slices in the proof of `lem:balanced`. -/
theorem periodicCAlpha_smooth_upgrade {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (hf : ContDiff ℝ ∞ f.toFun) (hα : α ≤ 1) (n : ℕ) :
    ∃ g : LittlePeriodicCAlphaFunction a N n α, g.val.toFun = f.toFun := by
  have hjet (j : ℕ) : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) → ‖iteratedFDeriv ℝ j f.toFun x‖ ≤ C := by
    have hcont : Continuous (fun x : Fin a → ℝ ↦
        iteratedFDeriv ℝ j f.toFun (toLp 2 x)) :=
      (hf.continuous_iteratedFDeriv (m := j) (by simp)).comp (PiLp.continuous_toLp _ _)
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
  obtain ⟨g, hg, hnorm⟩ := collar_smooth_holder_slice f.toFun hf f.periodic C
    (fun j hj ↦ hC j) hα D (fun x y ↦ hD (mem_univ _) (mem_univ _))
  exact ⟨g, hg⟩

#print axioms periodicCAlpha_smooth_upgrade

end GlobalEmbedding.Paper
