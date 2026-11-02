import Smoothing.ParameterGeometryJets
import Smoothing.WeightedActualOperations

/-! Native source-direction observations of joint jets, used by the literal
normalized primary coefficient. All auxiliary derivatives remain present. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep Es Y : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- One genuine source derivative costs precisely one joint derivative and
one slow weight. The fixed directional evaluation norm is kept explicit. -/
theorem actual_joint_directional_slow_jets
    (f : Ep × Es → Y) (v : Es) (O S : Set (Ep × Es)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) (j : ℕ) (ell M : ℝ) (hell : 0 < ell)
    (hb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k f z‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun z : Ep × Es => fderiv ℝ (fun x => f (z.1,x)) z.2 v) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2 v) z‖ ≤
          ‖ContinuousLinearMap.apply ℝ Y v‖ * M / ell := by
  let first := fun z : Ep × Es => fderiv ℝ (fun x => f (z.1,x)) z.2
  have hfirst := (incrementsJointSpatialJets_bridge f O hO hf).2.1
  let ev : (Es →L[ℝ] Y) →L[ℝ] Y := ContinuousLinearMap.apply ℝ Y v
  refine ⟨ev.contDiff.comp_contDiffOn hfirst,?_⟩
  intro k hk z hz
  have hfirstb : ell^k * ‖iteratedFDeriv ℝ k first z‖ ≤ M / ell := by
    apply (le_div_iff₀ hell).mpr
    calc
      _ = ell^(k+1) * ‖iteratedFDeriv ℝ k first z‖ := by rw [pow_succ]; ring
      _ ≤ ell^(k+1) * ‖iteratedFDeriv ℝ (k+1) f z‖ :=
        mul_le_mul_of_nonneg_left (spatial_first_jet_le hO hf (hSO hz) k) (by positivity)
      _ ≤ M := hb (k+1) (by omega) z hz
  have h := slow_linear_jet_bound ev O hO first hfirst k ell (M/ell)
    hell.le z (hSO hz) hfirstb
  simpa only [ev,first,Function.comp_def,ContinuousLinearMap.apply_apply,mul_div_assoc] using h

/-- Native joint addition retains the true same-order budgets. -/
theorem actual_joint_slow_add_jet_bound
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f g : X → Z) (k : ℕ) (ell Mf Mg : ℝ) (hell : 0 ≤ ell) (x : X)
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hfb : ell^k * ‖iteratedFDeriv ℝ k f x‖ ≤ Mf)
    (hgb : ell^k * ‖iteratedFDeriv ℝ k g x‖ ≤ Mg) :
    ell^k * ‖iteratedFDeriv ℝ k (fun y => f y + g y) x‖ ≤ Mf + Mg := by
  rw [fun_iteratedFDeriv_add_apply hf hg]
  calc
    _ ≤ ell^k * (‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hell k)
    _ = ell^k * ‖iteratedFDeriv ℝ k f x‖ + ell^k * ‖iteratedFDeriv ℝ k g x‖ := by ring
    _ ≤ Mf+Mg := add_le_add hfb hgb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_directional_slow_jets
