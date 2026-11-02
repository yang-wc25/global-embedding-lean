import Smoothing.ParameterGlobalEstimates
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Geometric input jets from the original cutoff and transition derivatives

Restricting a true joint derivative to spatial directions is a fixed norm-one
operation. This gives one- and two-derivative shifts only on geometric data.
No extra pure parameter derivatives are imposed on the map being smoothed.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

section Extraction
variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Fixed restriction of a full derivative to actual source directions. -/
def spatialFirstRestriction : ((Ep × Es) →L[ℝ] Y) →L[ℝ] (Es →L[ℝ] Y) :=
  (ContinuousLinearMap.compL ℝ Es (Ep × Es) Y).flip (ContinuousLinearMap.inr ℝ Ep Es)

theorem spatialFirstRestriction_norm_le : ‖spatialFirstRestriction (Ep := Ep) (Es := Es) (Y := Y)‖ ≤ 1 := by
  have hinr : ‖ContinuousLinearMap.inr ℝ Ep Es‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L.comp (ContinuousLinearMap.inr ℝ Ep Es)‖ ≤ 1 * ‖L‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg L])

/-- All extra joint derivatives of the first actual source jet are controlled
by the next full geometric derivative, including degenerate source dimension. -/
theorem spatial_first_jet_le {f : Ep × Es → Y} {O : Set (Ep × Es)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Ep × Es => fderiv ℝ (fun x => f (y.1,x)) y.2) z‖ ≤
      ‖iteratedFDeriv ℝ (k+1) f z‖ := by
  have heq : (fun y : Ep × Es => fderiv ℝ (fun x => f (y.1,x)) y.2) =ᶠ[𝓝 z]
      spatialFirstRestriction ∘ fderiv ℝ f := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact (incrementsJointSpatialJets_bridge f O hO hf).1 y hy
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  have hder := hf.fderiv_of_isOpen hO (m := ∞) (by simp)
  have h := (spatialFirstRestriction (Ep := Ep) (Es := Es) (Y := Y)).norm_iteratedFDeriv_comp_left
    (hder.contDiffAt (hO.mem_nhds hz)) (n := k) (by simp)
  apply h.trans
  rw [← norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (spatialFirstRestriction_norm_le (Ep := Ep) (Es := Es) (Y := Y)) (norm_nonneg _)

/-- Restrict the first source-jet field again: the second true source derivative
costs exactly two full derivatives of the geometric function. -/
theorem spatial_second_jet_le {f : Ep × Es → Y} {O : Set (Ep × Es)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (y.1,x))) y.2) z‖ ≤
      ‖iteratedFDeriv ℝ (k+2) f z‖ := by
  have hfirst := (incrementsJointSpatialJets_bridge f O hO hf).2.1
  exact (spatial_first_jet_le hO hfirst hz k).trans (spatial_first_jet_le hO hf hz (k+1))

end Extraction

section ProductBounds
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A convenient finite-product estimate for true joint jets. -/
theorem parameter_prod_jet_le {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ‖iteratedFDeriv ℝ k f x‖ ≤ A) (hgb : ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => (f y,g y)) x‖ ≤ A+B := by
  rw [iteratedFDeriv_prodMk hf hg (by simp), ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hfa.trans (le_add_of_nonneg_right hB)) (hgb.trans (le_add_of_nonneg_left hA))

end ProductBounds

#print axioms spatial_first_jet_le
#print axioms spatial_second_jet_le
#print axioms parameter_prod_jet_le
end
end GlobalEmbedding.Continuation
