import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds

/-!
# Global derivative control by the corresponding periodic supremum

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 382.
DAG node: `balanced-holder-derivative-sup-global`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual fundamental-cube supremum of a jet bounds that jet on every Euclidean lift.

Proof: integer translation commutes with iterated differentiation. Reduce each coordinate to
its fractional part, then apply the finite real supremum bound on the fundamental cube.
Source: the periodic Hölder norm in the proof of `lem:balanced`. -/
theorem periodicCAlpha_derivative_sup_global {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (j : ℕ) (hj : j ≤ k)
    (x : EuclideanSpace ℝ (Fin a)) :
    ‖iteratedFDeriv ℝ j f.toFun x‖ ≤
      sSup {r : ℝ | ∃ z : EuclideanSpace ℝ (Fin a),
        (∀ i, z i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun z‖} := by
  let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
  have hy : ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
    fun i ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hxy : y + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by
    ext i
    simp [y, Int.fract_add_floor]
  have hfxy : iteratedFDeriv ℝ j f.toFun x = iteratedFDeriv ℝ j f.toFun y := by
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z (fun i ↦ ⌊x i⌋))
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) j
      (toLp 2 (fun i ↦ (⌊x i⌋ : ℝ))) y
    simpa only [heq, hxy] using ht.symm
  rw [hfxy]
  exact le_csSup ((periodicCAlpha_supremum_bounds f).1 j hj) ⟨y, hy, rfl⟩

#print axioms periodicCAlpha_derivative_sup_global

end GlobalEmbedding.Paper
