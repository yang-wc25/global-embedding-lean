import GlobalEmbedding.Paper.PeriodicCAlphaFunction
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Every finite jet of an actual smooth periodic lift is globally Lipschitz

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-smooth-jet-lipschitz`.
-/

open Set WithLp
open scoped ContDiff NNReal

namespace GlobalEmbedding.Paper

/-- Each finite jet of a genuinely smooth periodic lift has a finite global Lipschitz constant.

Proof: continuity bounds the next jet on the compact coordinate cube. Integer periodicity
of that jet extends the bound globally. The operator norm of the derivative of the present
jet is the next jet norm, so the real mean value theorem supplies its Lipschitz constant.
Source: smooth translation estimates in the proof of `lem:balanced`. -/
theorem periodicCAlpha_smooth_jet_lipschitz {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (hf : ContDiff ℝ ∞ f.toFun) (j : ℕ) :
    ∃ L : ℝ≥0, LipschitzWith L (iteratedFDeriv ℝ j f.toFun) := by
  have hcont : Continuous (fun x : Fin a → ℝ ↦
      iteratedFDeriv ℝ (j + 1) f.toFun (toLp 2 x)) :=
    (hf.continuous_iteratedFDeriv (m := j + 1) (by simp)).comp (PiLp.continuous_toLp _ _)
  have hcompact : IsCompact (Icc (0 : Fin a → ℝ) 1) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  have hglobal (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ (j + 1) f.toFun x‖ ≤ C := by
    let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
    have hy : ofLp y ∈ Icc (0 : Fin a → ℝ) 1 :=
      ⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩
    have hxy : y + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by
      ext i
      simp [y, Int.fract_add_floor]
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z (fun i ↦ ⌊x i⌋))
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) (j + 1)
      (toLp 2 (fun i ↦ (⌊x i⌋ : ℝ))) y
    have hjxy : iteratedFDeriv ℝ (j + 1) f.toFun x =
        iteratedFDeriv ℝ (j + 1) f.toFun y := by
      simpa only [heq, hxy] using ht.symm
    rw [hjxy]
    exact hC (ofLp y) hy
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hglobal 0)
  refine ⟨⟨C, hC0⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast ENat.natCast_lt_top j))
  intro x
  change ‖fderiv ℝ (iteratedFDeriv ℝ j f.toFun) x‖ ≤ C
  rw [norm_fderiv_iteratedFDeriv]
  exact hglobal x

#print axioms periodicCAlpha_smooth_jet_lipschitz

end GlobalEmbedding.Paper
