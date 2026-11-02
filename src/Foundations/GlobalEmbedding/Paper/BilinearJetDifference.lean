import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A Leibniz difference estimate using exactly the declared differentiability order

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-bilinear-jet-difference`.
-/

namespace GlobalEmbedding.Paper

/-- A genuine bilinear product's n-th jet difference satisfies the Leibniz difference norm bound,
using C^n inputs only.

Translate one endpoint to the other. The shifted product difference equals the sum of the
product of the shifted first-factor difference with the shifted second factor, and the product
of the original first factor with the shifted second-factor difference. Differentiate this
exact function identity n times and apply Mathlib's existing bilinear derivative norm bound.
Translation identifies all difference jets at the common point with actual endpoint jet
subtractions. Source: the Hölder product estimate in `lem:balanced`. -/
theorem bilinear_jet_difference_bound
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (n : ℕ) (f : X → E) (g : X → F)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x y : X) :
    ‖iteratedFDeriv ℝ n (fun z ↦ B (f z) (g z)) x -
        iteratedFDeriv ℝ n (fun z ↦ B (f z) (g z)) y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ + ‖iteratedFDeriv ℝ i f y‖ *
          ‖iteratedFDeriv ℝ (n - i) g x - iteratedFDeriv ℝ (n - i) g y‖) := by
  let h := x - y
  let df (z : X) := f (z + h) - f z
  let sg (z : X) := g (z + h)
  let dg (z : X) := g (z + h) - g z
  let P (z : X) := B (f z) (g z)
  have hyh : y + h = x := by dsimp [h]; abel
  have hfs : ContDiff ℝ n (fun z ↦ f (z + h)) := hf.comp (contDiff_id.add contDiff_const)
  have hgs : ContDiff ℝ n sg := hg.comp (contDiff_id.add contDiff_const)
  have hdf : ContDiff ℝ n df := hfs.sub hf
  have hdg : ContDiff ℝ n dg := hgs.sub hg
  have hP : ContDiff ℝ n P := (B.contDiff.comp hf).clm_apply hg
  have hPs : ContDiff ℝ n (fun z : X ↦ P (z + h)) :=
    hP.comp (contDiff_id.add contDiff_const)
  have hP₁ : ContDiff ℝ n (fun z ↦ B (df z) (sg z)) := (B.contDiff.comp hdf).clm_apply hgs
  have hP₂ : ContDiff ℝ n (fun z ↦ B (f z) (dg z)) := (B.contDiff.comp hf).clm_apply hdg
  have hidentity : (fun z ↦ P (z + h) - P z) =
      (fun z ↦ B (df z) (sg z) + B (f z) (dg z)) := by
    funext z
    dsimp [P, df, sg, dg]
    simp only [map_sub, sub_apply]
    abel
  have hjet := congrArg (fun Q : X → G ↦ iteratedFDeriv ℝ n Q y) hidentity
  change iteratedFDeriv ℝ n ((fun z ↦ P (z + h)) - P) y =
    iteratedFDeriv ℝ n ((fun z ↦ B (df z) (sg z)) + (fun z ↦ B (f z) (dg z))) y at hjet
  rw [iteratedFDeriv_sub_apply hPs.contDiffAt hP.contDiffAt,
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) n h y, hyh,
    iteratedFDeriv_add_apply hP₁.contDiffAt hP₂.contDiffAt] at hjet
  have hdfjet (i : ℕ) (hi : i ≤ n) : iteratedFDeriv ℝ i df y =
      iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y := by
    change iteratedFDeriv ℝ i ((fun z ↦ f (z + h)) - f) y = _
    rw [iteratedFDeriv_sub_apply (hfs.of_le (by exact_mod_cast hi)).contDiffAt
      (hf.of_le (by exact_mod_cast hi)).contDiffAt,
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) i h y, hyh]
  have hsgjet (i : ℕ) : iteratedFDeriv ℝ i sg y = iteratedFDeriv ℝ i g x := by
    dsimp [sg]
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) i h y, hyh]
  have hdgjet (i : ℕ) (hi : i ≤ n) : iteratedFDeriv ℝ i dg y =
      iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y := by
    change iteratedFDeriv ℝ i (sg - g) y = _
    rw [iteratedFDeriv_sub_apply (hgs.of_le (by exact_mod_cast hi)).contDiffAt
      (hg.of_le (by exact_mod_cast hi)).contDiffAt, hsgjet]
  calc
    _ = ‖iteratedFDeriv ℝ n (fun z ↦ B (df z) (sg z)) y +
        iteratedFDeriv ℝ n (fun z ↦ B (f z) (dg z)) y‖ := congrArg norm hjet
    _ ≤ ‖iteratedFDeriv ℝ n (fun z ↦ B (df z) (sg z)) y‖ +
        ‖iteratedFDeriv ℝ n (fun z ↦ B (f z) (dg z)) y‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i df y‖ * ‖iteratedFDeriv ℝ (n - i) sg y‖) +
        (‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (n - i) dg y‖) :=
      add_le_add (B.norm_iteratedFDeriv_le_of_bilinear hdf hgs y le_rfl)
        (B.norm_iteratedFDeriv_le_of_bilinear hf hdg y le_rfl)
    _ = _ := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdfjet i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), hsgjet,
        hdgjet (n - i) (Nat.sub_le _ _)]
      ring

#print axioms bilinear_jet_difference_bound

end GlobalEmbedding.Paper
