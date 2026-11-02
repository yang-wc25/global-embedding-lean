import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Actual ordered scalar coordinate partials

Source: `literature/parallelizable-stable-plus-one/main.tex`, notation225–238.
Only the actual native repeated scalar coordinate derivative is identified here;
no analyticity, global smooth extension, or permutation of coordinate words is assumed.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Actual repeated within-coordinate scalar partial in the specified finite word.
The empty word is the original component, including in source dimension zero. -/
noncomputable def coordinateWordPartialWithin {n : ℕ} : (k : ℕ) → (Fin k → Fin n) →
    ((Fin n → ℝ) → ℝ) → Set (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, f, _, x => f x
  | k + 1, σ, f, U, x => lineDerivWithin ℝ
      (coordinateWordPartialWithin k (Fin.tail σ) f U) U x (Pi.single (σ 0) 1)

/-- On an open coordinate domain, the literal ordered partial is the SAME ordered
basis evaluation of the actual iterated Fréchet derivative. Only local smoothness
on U is required, so the chosen ambient extension need not be globally smooth. -/
theorem coordinateWordPartialWithin_eq_iteratedFDerivWithin {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (σ : Fin k → Fin n)
    (x : Fin n → ℝ) (hx : x ∈ U) :
    coordinateWordPartialWithin k σ f U x =
      iteratedFDerivWithin ℝ k f U x (fun a ↦ Pi.single (σ a) 1) := by
  induction k generalizing x with
  | zero => simp [coordinateWordPartialWithin]
  | succ k ih =>
    rw [coordinateWordPartialWithin]
    rw [lineDerivWithin_congr' (fun y hy ↦ ih (Fin.tail σ) y hy) hx]
    rw [lineDerivWithin_of_isOpen hU hx]
    have hdwithin := hf.differentiableOn_iteratedFDerivWithin (m := k)
      (by exact_mod_cast ENat.natCast_lt_top k) hU.uniqueDiffOn x hx
    have hd := hdwithin.differentiableAt (hU.mem_nhds hx)
    rw [(hd.continuousMultilinear_apply_const _).lineDeriv_eq_fderiv]
    rw [fderiv_continuousMultilinear_apply_const_apply hd]
    rw [← fderivWithin_of_isOpen hU hx]
    exact (iteratedFDerivWithin_succ_apply_left (𝕜 := ℝ) (f := f) (s := U)
      (x := x) (fun a ↦ Pi.single (σ a) 1)).symm

/-- The same actual scalar partial equals the ambient derivative at every point of
an open domain, without a smooth ambient extension assumption. -/
theorem coordinateWordPartialWithin_eq_iteratedFDeriv {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (σ : Fin k → Fin n)
    (x : Fin n → ℝ) (hx : x ∈ U) :
    coordinateWordPartialWithin k σ f U x =
      iteratedFDeriv ℝ k f x (fun a ↦ Pi.single (σ a) 1) := by
  rw [coordinateWordPartialWithin_eq_iteratedFDerivWithin f U hU hf k σ x hx,
    iteratedFDerivWithin_of_isOpen k hU hx]

/-- The native scalar partial of the literal c-th coordinate of a finite-coordinate
map is exactly the c-th coordinate of its actual derivative, on the SAME local domain. -/
theorem coordinateWordPartialWithin_component {n q : ℕ}
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (σ : Fin k → Fin n)
    (c : Fin q) (x : Fin n → ℝ) (hx : x ∈ U) :
    coordinateWordPartialWithin k σ (fun y ↦ f y c) U x =
      iteratedFDeriv ℝ k f x (fun a ↦ Pi.single (σ a) 1) c := by
  have hc : ContDiffOn ℝ ∞ (fun y ↦ f y c) U :=
    (contDiffOn_pi.mp hf) c
  rw [coordinateWordPartialWithin_eq_iteratedFDeriv (fun y ↦ f y c) U hU hc k σ x hx]
  let proj : (Fin q → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj c
  have h := proj.iteratedFDeriv_comp_left
    (hf.contDiffAt (hU.mem_nhds hx)) (i := k) (by simp)
  exact congrArg (fun p ↦ p (fun a ↦ Pi.single (σ a) 1)) h

end GlobalEmbedding.Paper
