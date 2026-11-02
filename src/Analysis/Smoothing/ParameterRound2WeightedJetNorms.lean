import Smoothing.ParameterRound2InitialWeights
import GlobalEmbedding.Offline.ModelCoordinateNorms

/-!
# Actual scaled joint jets give the original weighted atlas norm

All derivatives below are derivatives of the same function. The original
cumulative Cj maximum is retained, with only the explicit m+1 derivative
levels in its weighted sum. Native coordinate changes retain their actual
linear operator costs. No atlas or primary cardinality appears.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι : Type*} [Fintype ι] {a q : ℕ}

theorem parameterRound2_paperAtlasCj_le_of_weighted_jets
    (j : ℕ) (scale K : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hjet : ∀ i, ∀ k ≤ j, ∀ x ∈ S i, scale^k * ‖iteratedFDeriv ℝ k (f i) x‖ ≤ K) :
    paperAtlasCj j f O S ≤ ENNReal.ofReal (K / scale^j) := by
  apply paperAtlasCj_le_of_jet_bound j f O S hO hSO hf
  intro i k hk x hx
  apply (le_div_iff₀ (pow_pos hscale j)).2
  calc
    _ = scale^j * ‖iteratedFDeriv ℝ k (f i) x‖ := mul_comm _ _
    _ ≤ scale^k * ‖iteratedFDeriv ℝ k (f i) x‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hscale.le hscale1 hk) (norm_nonneg _)
    _ ≤ K := hjet i k hk x hx

/-- No finiteness premise is needed: the actual scaled jets prove it before
the original weighted norm is converted to a real number. -/
theorem parameterRound2_paperAtlasWeighted_le_of_weighted_jets
    (m : ℕ) (scale K : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hK : 0 ≤ K)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hjet : ∀ i, ∀ k ≤ m, ∀ x ∈ S i, scale^k * ‖iteratedFDeriv ℝ k (f i) x‖ ≤ K) :
    paperAtlasWeighted 0 m scale f O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 m scale f O S).toReal ≤ (m+1)*K := by
  have hc (j : ℕ) (hj : j ≤ m) := parameterRound2_paperAtlasCj_le_of_weighted_jets
    j scale K hscale hscale1 f O S hO hSO hf (fun i k hk => hjet i k (hk.trans hj))
  have hfinite := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 m scale f O S
    (by simpa only [Nat.add_zero] using ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc m le_rfl))
  refine ⟨hfinite, ?_⟩
  rw [paperAtlasWeighted_toReal 0 m scale hscale.le f O S hfinite]
  calc
    _ ≤ ∑ _j ∈ Finset.range (m+1), K := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc j (by simpa using hj))
      rw [ENNReal.toReal_ofReal (div_nonneg hK (pow_nonneg hscale.le j))] at hh
      simpa only [Nat.add_zero, mul_div_cancel₀ _ (pow_ne_zero j hscale.ne')] using
        mul_le_mul_of_nonneg_left hh (pow_nonneg hscale.le j)
    _ = _ := by simp [nsmul_eq_mul]

/-- Same scaled jets on the native model imply the literal original full
coordinate weighted norm, with the actual inverse model factor. -/
theorem parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] (Fin a → ℝ)) (m : ℕ)
    (scale K : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hK : 0 ≤ K)
    (f : ι → E → Fin q → ℝ) (O S : ι → Set E)
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hjet : ∀ i, ∀ k ≤ m, ∀ x ∈ S i, scale^k * ‖iteratedFDeriv ℝ k (f i) x‖ ≤ K) :
    paperAtlasWeighted 0 m scale (modelCoordinateFamily e f)
      (modelCoordinateDomains e O) (modelCoordinateDomains e S) ≠ ⊤ ∧
      (paperAtlasWeighted 0 m scale (modelCoordinateFamily e f)
        (modelCoordinateDomains e O) (modelCoordinateDomains e S)).toReal ≤
          (m+1)*linearModelFactor e.symm m*K := by
  have hcost : 0 ≤ linearModelFactor e.symm m*K := mul_nonneg (linearModelFactor_nonneg _ _) hK
  have h := parameterRound2_paperAtlasWeighted_le_of_weighted_jets m scale
    (linearModelFactor e.symm m*K) hscale hscale1 hcost
    (modelCoordinateFamily e f) (modelCoordinateDomains e O) (modelCoordinateDomains e S)
    (modelCoordinateDomains_open e hO) (fun i _ hx => hSO i hx)
    (modelCoordinateFamily_contDiffOn e hf) ?_
  · exact ⟨h.1, by simpa only [mul_assoc] using h.2⟩
  intro i k hk x hx
  have hc := norm_iteratedFDeriv_comp_equiv_le e.symm (f i) k x
  change scale^k * ‖iteratedFDeriv ℝ k (f i ∘ e.symm) x‖ ≤ _
  calc
    _ ≤ scale^k * (‖iteratedFDeriv ℝ k (f i) (e.symm x)‖ * linearModelFactor e.symm k) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hscale.le k)
    _ = linearModelFactor e.symm k *
        (scale^k * ‖iteratedFDeriv ℝ k (f i) (e.symm x)‖) := by ring
    _ ≤ linearModelFactor e.symm m*K := mul_le_mul (linearModelFactor_mono e.symm hk)
      (hjet i k hk _ hx) (by positivity) (linearModelFactor_nonneg _ _)

#print axioms parameterRound2_paperAtlasWeighted_le_of_weighted_jets
#print axioms parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets
end
end GlobalEmbedding.Continuation
