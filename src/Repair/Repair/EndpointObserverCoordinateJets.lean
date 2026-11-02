import Repair.EndpointLocalFieldObserverJets
import Smoothing.ParameterRound2WeightedJetNorms

/-! Genuine source-first coordinate conversion and the original cumulative
weighted maximum.  Neither estimate introduces a chart-count factor. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology BigOperators ENNReal
namespace GlobalEmbedding.Continuation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {srcDim q : ℕ}

theorem repair_original_output_coordinate_jet
    (a : E ≃L[ℝ] (Fin srcDim → ℝ)) (c : F →L[ℝ] (Fin q → ℝ))
    (f : E → F) (O : Set E) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (x : Fin srcDim → ℝ) (hx : a.symm x ∈ O)
    (j : ℕ) (K : ℝ) (hb : ‖iteratedFDeriv ℝ j f (a.symm x)‖ ≤ K) :
    ‖iteratedFDeriv ℝ j (c ∘ f ∘ a.symm) x‖ ≤
      ‖c‖ * K * ‖a.symm.toContinuousLinearMap‖^j := by
  have hl := c.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds hx)) (n := j) (by simp)
  have hr := repair_linear_right_jet a.symm.toContinuousLinearMap (c ∘ f) O hO
    (c.contDiff.comp_contDiffOn hf) x hx j
  exact hr.trans (mul_le_mul_of_nonneg_right
    (hl.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg c))) (by positivity))

def repairOriginalJetPrefix (A : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), A k

theorem repairOriginalJetPrefix_nonneg (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (j : ℕ) :
    0 ≤ repairOriginalJetPrefix A j :=
  Finset.sum_nonneg (fun k _ => hA k)

theorem repairOriginalJetPrefix_bound (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    {k j : ℕ} (hkj : k ≤ j) : A k ≤ repairOriginalJetPrefix A j :=
  Finset.single_le_sum (fun l _ => hA l) (by simp; omega)

theorem repair_original_weighted_profile_from_jets
    {ι : Type*} [Fintype ι]
    (f : ι → (Fin srcDim → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin srcDim → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (hJet : ∀ i k x, x ∈ S i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A k)
    (j : ℕ) :
    paperAtlasWeighted 0 j 1 f O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j 1 f O S).toReal ≤ (j+1)*repairOriginalJetPrefix A j := by
  apply parameterRound2_paperAtlasWeighted_le_of_weighted_jets j 1
    (repairOriginalJetPrefix A j) zero_lt_one le_rfl (repairOriginalJetPrefix_nonneg A hA j)
    f O S hO hSO hf
  intro i k hk x hx
  simpa only [one_pow,one_mul] using
    (hJet i k x hx).trans (repairOriginalJetPrefix_bound A hA hk)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_output_coordinate_jet
#print axioms GlobalEmbedding.Continuation.repair_original_weighted_profile_from_jets
