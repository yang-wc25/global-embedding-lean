import Probes.ActualRefinementNormalizer
import Smoothing.WeightedActualOperations
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The actual refinement partition has all uniform weighted derivatives

The cutoffs are raw translated/rescaled bumps multiplied by one fixed smooth
reciprocal of their sum. Every budget here is proved for that literal formula.
The only counting constant is the native local 5^dim multiplicity.
-/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def actualRefinementBumpPrefix (j : ℕ) : ℝ :=
  1+∑ i ∈ Finset.range (j+1), actualRefinementBumpJetCost E i

theorem actualRefinementBumpPrefix_one_le (j : ℕ) : 1 ≤ actualRefinementBumpPrefix E j :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => actualRefinementBumpJetCost_nonneg E i))

theorem actualRefinementBumpJetCost_le_prefix {i j : ℕ} (hij : i ≤ j) :
    actualRefinementBumpJetCost E i ≤ actualRefinementBumpPrefix E j := by
  have hh := Finset.single_le_sum (s := Finset.range (j+1))
    (fun k _ => actualRefinementBumpJetCost_nonneg E k) (by simpa using hij : i ∈ Finset.range (j+1))
  exact hh.trans (le_add_of_nonneg_left zero_le_one)

def actualRefinementRawRangeCost : ℝ :=
  1+(5^Module.finrank ℝ E : ℕ)*actualRefinementBumpJetCost E 0

def actualRefinementInnerJetCost (j : ℕ) : ℝ :=
  1+(5^Module.finrank ℝ E : ℕ)*actualRefinementBumpPrefix E j

def actualRefinementOuterJetCost (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), actualRefinementReciprocalDerivativeCost (actualRefinementRawRangeCost E) i

theorem actualRefinementInnerJetCost_one_le (j : ℕ) : 1 ≤ actualRefinementInnerJetCost E j :=
  le_add_of_nonneg_right (mul_nonneg (by positivity) (zero_le_one.trans (actualRefinementBumpPrefix_one_le E j)))

theorem actualRefinementOuterJetCost_nonneg (j : ℕ) : 0 ≤ actualRefinementOuterJetCost E j :=
  Finset.sum_nonneg (fun i _ => actualRefinementReciprocalDerivativeCost_nonneg _ i)

def actualRefinementReciprocalCompositionCost (j : ℕ) : ℝ :=
  (j.factorial : ℝ)*actualRefinementOuterJetCost E j*(actualRefinementInnerJetCost E j)^j

theorem actualRefinementReciprocalCompositionCost_nonneg (j : ℕ) :
    0 ≤ actualRefinementReciprocalCompositionCost E j :=
  mul_nonneg (mul_nonneg (by positivity) (actualRefinementOuterJetCost_nonneg E j))
    (pow_nonneg (zero_le_one.trans (actualRefinementInnerJetCost_one_le E j)) j)

theorem actualRefinementRawSum_range_bound
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (x : E) :
    ‖actualRefinementRawSum E s r x‖ ≤ actualRefinementRawRangeCost E := by
  have hh := actualRefinementRawSum_weighted_jet E s r hr hsep 0 x
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero] at hh
  exact hh.trans (le_add_of_nonneg_left zero_le_one)

theorem actualRefinementReciprocalComposition_weighted_jet
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (j : ℕ) (x : E) :
    r^j*‖iteratedFDeriv ℝ j (actualRefinementReciprocal ∘ actualRefinementRawSum E s r) x‖ ≤
      actualRefinementReciprocalCompositionCost E j := by
  let e := slowDilation (D := E) r hr.ne'
  let Q := actualRefinementRawSum E s r ∘ e
  have hQ : ContDiff ℝ ∞ Q := (actualRefinementRawSum_contDiff E s r).comp e.contDiff
  have hQj (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDeriv ℝ k Q (e.symm x)‖ ≤ (actualRefinementInnerJetCost E j)^k := by
    rw [norm_iteratedFDeriv_slowDilation _ r hr k (e.symm x)]
    have hb := actualRefinementRawSum_weighted_jet E s r hr hsep k (r • e.symm x)
    have hh : (5^Module.finrank ℝ E : ℕ)*actualRefinementBumpJetCost E k ≤ actualRefinementInnerJetCost E j :=
      (mul_le_mul_of_nonneg_left (actualRefinementBumpJetCost_le_prefix E hkj) (by positivity)).trans
        (le_add_of_nonneg_left zero_le_one)
    exact (hb.trans hh).trans (le_self_pow₀ (actualRefinementInnerJetCost_one_le E j) (by omega))
  have hCj (k : ℕ) (hk : k ≤ j) :
      ‖iteratedFDeriv ℝ k actualRefinementReciprocal (Q (e.symm x))‖ ≤ actualRefinementOuterJetCost E j := by
    have hb := actualRefinementReciprocalDerivativeCost_bound (actualRefinementRawRangeCost E) k
      (Q (e.symm x)) (actualRefinementRawSum_range_bound E s r hr hsep _)
    apply hb.trans
    exact Finset.single_le_sum (fun i _ => actualRefinementReciprocalDerivativeCost_nonneg _ i)
      (by simpa using hk)
  have hb := norm_iteratedFDeriv_comp_le actualRefinementReciprocal_contDiff hQ
    (by simp : (j : ℕ∞ω) ≤ ∞) (e.symm x) hCj hQj
  change ‖iteratedFDeriv ℝ j
    ((actualRefinementReciprocal ∘ actualRefinementRawSum E s r) ∘ e) (e.symm x)‖ ≤ _ at hb
  rw [norm_iteratedFDeriv_slowDilation _ r hr j (e.symm x)] at hb
  have he : r • e.symm x = x := e.apply_symm_apply x
  rwa [he] at hb

def actualRefinementReciprocalPrefix (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), actualRefinementReciprocalCompositionCost E i

theorem actualRefinementReciprocalPrefix_nonneg (j : ℕ) : 0 ≤ actualRefinementReciprocalPrefix E j :=
  Finset.sum_nonneg (fun i _ => actualRefinementReciprocalCompositionCost_nonneg E i)

def actualRefinementCutoff (s : Finset E) (r : ℝ) (c : E) : E → ℝ :=
  fun x => actualRefinementBump E r c x * actualRefinementReciprocal (actualRefinementRawSum E s r x)

theorem actualRefinementCutoff_contDiff (s : Finset E) (r : ℝ) (c : E) :
    ContDiff ℝ ∞ (actualRefinementCutoff E s r c) :=
  (actualRefinementBump_contDiff E r c).mul
    (actualRefinementReciprocal_contDiff.comp (actualRefinementRawSum_contDiff E s r))

theorem actualRefinementCutoff_nonneg (s : Finset E) (r : ℝ) (c x : E) :
    0 ≤ actualRefinementCutoff E s r c x :=
  mul_nonneg (actualRefinementBump_nonneg E r c x) (actualRefinementReciprocal_nonneg _)

theorem actualRefinementCutoff_tsupport (s : Finset E) (r : ℝ) (hr : 0 < r) (c : E) :
    tsupport (actualRefinementCutoff E s r c) ⊆ closedBall c (2*r) := by
  rw [← actualRefinementBump_tsupport E r hr c]
  exact tsupport_mul_subset_left

theorem actualRefinementCutoff_sum (s : Finset E) (r : ℝ) (x : E) :
    (∑ c ∈ s, actualRefinementCutoff E s r c x) =
      actualRefinementRawSum E s r x * actualRefinementReciprocal (actualRefinementRawSum E s r x) := by
  unfold actualRefinementCutoff actualRefinementRawSum
  exact (Finset.sum_mul _ _ _).symm

theorem actualRefinementCutoff_sum_eq_one
    (s : Finset E) (r : ℝ) (hr : 0 < r) (K : Set E)
    (hcover : ∀ x ∈ K, ∃ c ∈ s, dist x c ≤ r) (x : E) (hx : x ∈ K) :
    (∑ c ∈ s, actualRefinementCutoff E s r c x) = 1 := by
  rw [actualRefinementCutoff_sum]
  exact actualRefinementReciprocal_exact _
    ((by norm_num : (1:ℝ)/2 ≤ 1).trans (actualRefinementRawSum_lower_on_cover E s r hr K hcover x hx))

theorem actualRefinementCutoff_le_one (s : Finset E) (r : ℝ) (c : E) (hc : c ∈ s) (x : E) :
    actualRefinementCutoff E s r c x ≤ 1 := by
  have hh := Finset.single_le_sum (fun a _ => actualRefinementCutoff_nonneg E s r a x) hc
  rw [actualRefinementCutoff_sum] at hh
  exact hh.trans (actualRefinementReciprocal_subunit _)

def actualRefinementCutoffJetCost (j : ℕ) : ℝ :=
  2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*actualRefinementBumpPrefix E j)*actualRefinementReciprocalPrefix E j

theorem actualRefinementCutoffJetCost_nonneg (j : ℕ) : 0 ≤ actualRefinementCutoffJetCost E j :=
  mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg
    (zero_le_one.trans (actualRefinementBumpPrefix_one_le E j)))) (actualRefinementReciprocalPrefix_nonneg E j)

theorem actualRefinementCutoff_weighted_jet
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (c x : E) (j : ℕ) :
    r^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff E s r c) x‖ ≤ actualRefinementCutoffJetCost E j := by
  apply slow_bilinear_jet_bound_norm (ContinuousLinearMap.mul ℝ ℝ) univ isOpen_univ
    (actualRefinementBump E r c) (actualRefinementReciprocal ∘ actualRefinementRawSum E s r)
    (actualRefinementBump_contDiff E r c).contDiffOn
    (actualRefinementReciprocal_contDiff.comp (actualRefinementRawSum_contDiff E s r)).contDiffOn
    j r (actualRefinementBumpPrefix E j) (actualRefinementReciprocalPrefix E j) hr.le x (mem_univ x)
  · intro k hk
    exact (actualRefinementBump_weighted_jet E r hr c x k).trans (actualRefinementBumpJetCost_le_prefix E hk)
  · intro k hk
    apply (actualRefinementReciprocalComposition_weighted_jet E s r hr hsep k x).trans
    exact Finset.single_le_sum (fun i _ => actualRefinementReciprocalCompositionCost_nonneg E i)
      (by simpa using hk)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualRefinementReciprocalComposition_weighted_jet
#print axioms GlobalEmbedding.Continuation.actualRefinementCutoff_weighted_jet
#print axioms GlobalEmbedding.Continuation.actualRefinementCutoff_sum_eq_one
