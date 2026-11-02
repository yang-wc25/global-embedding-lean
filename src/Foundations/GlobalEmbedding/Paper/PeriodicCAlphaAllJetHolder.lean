import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import GlobalEmbedding.Paper.PeriodicCAlphaQuotientBound
import GlobalEmbedding.Paper.CollarPeriodicHolderFromLipschitz
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual flat-torus Hölder control for every jet through the declared order

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-all-jet-holder-bound`.
-/

open WithLp
open scoped NNReal

namespace GlobalEmbedding.Paper

/-- Every jet through order k has an actual flat-torus α-Hölder bound controlled by the
original full C^{k,α} norm and the diameter factor, without an extra derivative assumption.

At the top order use the actual Holder quotient bound. At each lower order the next jet is
already controlled by the original norm; mean value gives global Lipschitz control. Integer
periodicity and the actual torus distance then give the quotient estimate. Bound both cases
by (1+D^(1−α))‖f‖. Source: Leibniz Hölder product estimate in `lem:balanced`. -/
theorem periodicCAlpha_all_jet_holder_bound {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D)
    (j : ℕ) (hj : j ≤ k) (x y : EuclideanSpace ℝ (Fin a))
    (hd : 0 < dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))) :
    ‖iteratedFDeriv ℝ j f.toFun x - iteratedFDeriv ℝ j f.toFun y‖ /
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ^ α ≤
      (1 + D ^ (1 - α)) * ‖f‖ := by
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hpow : 0 ≤ D ^ (1 - α) := Real.rpow_nonneg hD0 _
  rcases lt_or_eq_of_le hj with hlt | rfl
  · have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j f.toFun) :=
      f.contDiff.differentiable_iteratedFDeriv (by exact_mod_cast hlt)
    have hlip : LipschitzWith ‖f‖₊ (iteratedFDeriv ℝ j f.toFun) := by
      apply lipschitzWith_of_nnnorm_fderiv_le hdiff
      intro z
      change ‖fderiv ℝ (iteratedFDeriv ℝ j f.toFun) z‖ ≤ ‖f‖
      rw [norm_fderiv_iteratedFDeriv]
      exact periodicCAlpha_global_jet_bound f (j + 1) (Nat.succ_le_of_lt hlt) z
    have hperiodic (z : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
        iteratedFDeriv ℝ j f.toFun (z + toLp 2 (fun i ↦ (m i : ℝ))) =
          iteratedFDeriv ℝ j f.toFun z := by
      have heq : (fun w ↦ f.toFun (w + toLp 2 (fun i ↦ (m i : ℝ)))) = f.toFun :=
        funext (fun w ↦ f.periodic w m)
      have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) j
        (toLp 2 (fun i ↦ (m i : ℝ))) z
      simpa only [heq] using ht.symm
    have hbound := collar_periodic_holder_from_lipschitz (iteratedFDeriv ℝ j f.toFun)
      hperiodic ‖f‖₊ hlip α hα D hdiam x y hd
    change _ ≤ ‖f‖ * D ^ (1 - α) at hbound
    exact hbound.trans (by nlinarith [norm_nonneg f])
  · have hbound := periodicCAlpha_quotient_bound f x y hd
    change _ ≤ ‖f‖ at hbound
    exact hbound.trans (by nlinarith [norm_nonneg f])

#print axioms periodicCAlpha_all_jet_holder_bound

end GlobalEmbedding.Paper
