import GlobalEmbedding.Paper.PeriodicCAlphaSmoothJetLipschitz
import GlobalEmbedding.Paper.PeriodicCAlphaTranslate
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import GlobalEmbedding.Paper.CollarHolderNormFromJetBounds

/-!
# A full Hölder-norm estimate for actual smooth translation differences

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-smooth-translation-norm-bound`.
-/

open Set WithLp
open scoped ContDiff NNReal

namespace GlobalEmbedding.Paper

/-- For a genuine smooth periodic lift, actual translation differences are O(‖h‖) in the FULL
original Hölder norm, for every α≤1.

Proof: every jet is globally Lipschitz. Thus each jet of the translation difference is bounded
by its Lipschitz constant times ‖h‖. The same bound one order higher makes its top jet
Lipschitz with a constant of that order. Apply the published actual jet-to-Hölder norm estimate
on the compact flat torus and collect the finitely many constants.
Source: smooth periodic approximation in the translation argument of `lem:balanced`. -/
theorem periodicCAlpha_smooth_translate_bound {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (hf : ContDiff ℝ ∞ f.toFun) (hα : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : EuclideanSpace ℝ (Fin a),
      ‖periodicCAlphaTranslate h f - f‖ ≤ C * ‖h‖ := by
  choose L hL using periodicCAlpha_smooth_jet_lipschitz f hf
  have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
    have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
        PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
      Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
    rw [← hrange]
    exact isCompact_range (PiLp.continuous_toLp _ _)
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  have hdiam (x y : EuclideanSpace ℝ (Fin a)) :
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D :=
    hD (mem_univ _) (mem_univ _)
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  let C := (∑ j ∈ Finset.range (k + 1), (L j : ℝ)) + (L (k + 1) : ℝ) * D ^ (1 - α)
  refine ⟨C, add_nonneg (Finset.sum_nonneg (fun j hj ↦ (L j).coe_nonneg))
    (mul_nonneg (L (k + 1)).coe_nonneg (Real.rpow_nonneg hD0 _)), ?_⟩
  intro h
  have hsubfun : (periodicCAlphaTranslate h f - f).toFun =
      (fun x ↦ f.toFun (x + h)) - f.toFun := by
    exact congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val)
      ((periodicCAlphaCarrierEquiv a N k α).addEquiv.map_sub (periodicCAlphaTranslate h f) f)
  have hshift : ContDiff ℝ ∞ (fun x ↦ f.toFun (x + h)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hdelta : ContDiff ℝ ∞ (periodicCAlphaTranslate h f - f).toFun := by
    rw [hsubfun]
    exact hshift.sub hf
  have hjet (j : ℕ) (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (periodicCAlphaTranslate h f - f).toFun x‖ ≤ (L j : ℝ) * ‖h‖ := by
    rw [hsubfun, iteratedFDeriv_sub_apply (hshift.of_le (by simp)).contDiffAt
      (hf.of_le (by simp)).contDiffAt, iteratedFDeriv_comp_add_right (𝕜 := ℝ) j h x]
    simpa only [dist_eq_norm, add_sub_cancel_left] using (hL j).dist_le_mul (x + h) x
  let K : ℝ≥0 := ⟨(L (k + 1) : ℝ) * ‖h‖, mul_nonneg (L (k + 1)).coe_nonneg (norm_nonneg _)⟩
  have htop : LipschitzWith K
      (iteratedFDeriv ℝ k (periodicCAlphaTranslate h f - f).toFun) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      (hdelta.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k))
    intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ k (periodicCAlphaTranslate h f - f).toFun) x‖ ≤
      (L (k + 1) : ℝ) * ‖h‖
    rw [norm_fderiv_iteratedFDeriv]
    exact hjet (k + 1) x
  have hnorm := collar_holder_norm_from_jet_bounds (periodicCAlphaTranslate h f - f)
    (fun j ↦ (L j : ℝ) * ‖h‖) (fun j hj x hx ↦ hjet j x) K htop hα D hdiam
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), (L j : ℝ) * ‖h‖) +
        ((L (k + 1) : ℝ) * ‖h‖) * D ^ (1 - α) := hnorm
    _ = C * ‖h‖ := by dsimp [C]; rw [← Finset.sum_mul]; ring

#print axioms periodicCAlpha_smooth_translate_bound

end GlobalEmbedding.Paper
